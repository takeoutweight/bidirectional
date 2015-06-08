(ns bidirectional.bidirectional
  (:require [clojure.tools.analyzer :as ta]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer :all]
            [clojure.tools.analyzer.passes.elide-meta :as taem]
            [clojure.tools.analyzer.jvm :as taj]
            [clojure.jvm.tools.analyzer.emit-form :as tae]
            [clojure.core.match :refer [match]]))

(defmacro <<-
  "reversed version of ->> for do-notation-esque things.
   Forms are placed as the last argument of the PRECEEDING form.
   eg: (<<- (1 2) (3 4) (5 6)) goes to (1 2 (3 4 (5 6)))
   eg: (<<- (if (nil? a) :early-exit) (inc a)) ->
            (if (nil? a) :early-exit (inc a))
   Nice for deeply right-nested expressions."
  [& forms]
  `(->> ~@(reverse forms)))

(def ann) ;; Unbound - keyword reserved for type annotations.

(defn ctx-conj
  [ctx ctx-elem]
  (conj ctx ctx-elem))

(defn ctx-concat
  [& ctxs]
  (vec (apply concat ctxs)))

(defn ctx-break
  "returns [ctx-left ctx-right]"
  [ctx ctx-elem]
  (let [idx (ffirst (filter (fn [[i e]] (if (= e ctx-elem) i nil)) (map-indexed vector ctx)))]
    (if (nil? idx) (throw (ex-info "Can't find element to break" {:ctx ctx :ctx-elem ctx-elem}))
        [(subvec ctx 0 idx)
         (subvec ctx (inc idx) (count ctx))])))

(defn ctx-drop
  "I think this drops everything to the right of elem, including elem."
  [ctx ctx-elem]
  (first (ctx-break ctx ctx-elem)))

(defn find-var-type ;; Context.hs
  "Looks up a var in context - returns its type or nil"
  [ctx var-name]
  (:c-typ (first (filter (fn [e] (= (:c-var-name e) var-name)) ctx))))

(defn existentials
  "returns a set of the existential var names"
  [ctx]
  (into #{} (map :c-var-name (filter #(#{:c-exists :c-exists-solved} (:c-op %)) ctx))))

(defmulti type-wf (fn [ctx typ] (:t-op typ)))
(defmethod type-wf :t-unit [ctx typ]
  true)
(defmethod type-wf :t-var [ctx typ]
  (contains? (into #{} (map :c-var-name (filter #(= :c-forall (:c-op %)) ctx)))
             (:t-var-name typ)))
(defmethod type-wf :t-fn [ctx typ]
  (and (type-wf ctx (:t-param typ))
       (type-wf ctx (:t-ret typ))))
(defmethod type-wf :t-forall [ctx typ]
  (type-wf (ctx-conj ctx {:c-op :c-forall :c-var-name (:t-var-name typ)})
           (:t-ret typ)))
(defmethod type-wf :t-exists [ctx typ]
  (contains? (existentials ctx)
             (:t-var-name typ)))

;;; FIXME I'm not sure this is what this fn is doing? I think we're effectively
;;; resolving to the "leftmost" unsolved existential, even if it's not yet
;;; resolved to a monotype. Is this right/ok?
(defn find-solved ;; findSolved Context.hs
  "returns nil or the solved monotype"
  [ctx var-name]
  (:c-typ (first (filter (fn [c-elem] (and (= :c-exists-solved (:c-op c-elem))
                                           (= var-name (:c-var-name c-elem))))
                         ctx))))

(defn unsolved
  "returns set of unsolved existentials"
  [ctx]
  (into #{} (filter #(#{:c-exists} (:c-op %)) ctx)))

(defn update-keys
  "update-in over parallel sibling keys, (i.e. not nested keys like update-in)"
  [m ks f]
  (reduce (fn [m k] (update-in m [k] f)) m ks))

;;; Types are functorial
(defmulti map-type (fn [f t] (:t-op t)))
(defmethod map-type :t-unit   [f t] t)
(defmethod map-type :t-var    [f t] t)
(defmethod map-type :t-forall [f t] (update-keys t [:t-ret] f))
(defmethod map-type :t-fn     [f t] (update-keys t [:t-param :t-ret] f))

(defn update-type
  "arg flipped map-type"
  [t f] (map-type f t))

(defn type-apply ;; apply Context.hs
  "looks up a type with the solved existentals replaced with what they're solved with?
   takes a type and returns a type."
  [ctx typ]
  (if (= :t-exists (:t-op typ))
    (if-let [typ' (find-solved ctx (:t-var-name typ))]
      (type-apply ctx typ')
      typ)
    (map-type #(type-apply ctx %) typ)))

;;; TODO Might be handy to renumber the context too (for showing unsolved existentials etc)
(defn renumber-varnames
  "renames gensyms to something stable. Recognizes gensyms via regex so just clips off post-fix number"
  [typ]
  (let [env (atom {})] ;; exists can add names anywhere.
    (letfn [(fresh [typ]
              (let [old-name (:t-var-name typ)
                    new-base (subs (str old-name) 0 (- (count (str old-name))
                                                       (count (re-find #"[0-9_]*" (str/reverse (str old-name))))))
                    new-renames (into #{} (vals @env))
                    new-name (->> (for [i (drop 1 (range))] (str new-base "_" i))
                                  (cons new-base)
                                  (map symbol)
                                  (remove #(contains? new-renames %))
                                  (first))]
                (swap! env assoc old-name new-name)
                new-name))
            (renumber
              [typ]
              (case (:t-op typ)
                :t-forall
                (->> (assoc-in typ [:t-var-name] (fresh typ))
                     (map-type renumber))
                :t-exists (if-let [new-name (get @env (:t-var-name typ))] ;; existentials implicitly range over entire expression
                            (assoc-in typ [:t-var-name] new-name)
                            (assoc-in typ [:t-var-name] (fresh typ)))
                :t-var (if-let [new-name (get @env (:t-var-name typ))]
                         (assoc-in typ [:t-var-name] new-name)
                         (throw (ex-info "No name provided for var " {:typ typ})))
                (map-type renumber typ)))]
      (renumber typ))))

(defn analyze-annotations
  "changes analysis of forms (bidirectional.bidirectional/ann expr type) from :invoke to
  :annotation"
  [expr]
  (cond
    (and (= :invoke (:op expr))
         (= :var (:op (:fn expr)) )
         (= #'bidirectional.bidirectional/ann (:var (:fn expr))))
    , (do
        (assert (= 2 (count (:args expr))) "annotation should have two arguments: (ann expr type)")
        (assert (:literal? (second (:args expr))) "second argument to ann must be a type literal")
        (-> expr
            (assoc :op :annotation)
            (assoc :type (:val (second (:args expr))))
            (assoc :expr (analyze-annotations (first (:args expr))))
            (assoc :children [:expr])
            (dissoc :args :fn :result :tag :o-tag)))
    (vector? expr) (vec (map analyze-annotations expr)) ;; eg: for :args children traversal
    :else (reduce (fn [e key]
                    (update-in e [key] analyze-annotations))
                  expr
                  (:children expr))))

(defn c-marker
  "constructor"
  [c-var-name]
  {:c-op :c-exists :c-var-name c-var-name})

(defn c-exists
  "constructor"
  [c-var-name]
  {:c-op :c-exists :c-var-name c-var-name})

(defn c-exists-solved
  "constructor"
  [c-var-name typ]
  {:c-op :c-exists-solved :c-var-name c-var-name :c-typ typ})

(defmulti monotype? :t-op)
(defmethod monotype? :t-unit [_] true)
(defmethod monotype? :t-var  [_] true)
(defmethod monotype? :t-exists [_] true)
(defmethod monotype? :t-forall [_] false)
(defmethod monotype? :t-fn [typ] (and (monotype? (:t-param typ))
                                      (monotype? (:t-ret typ))))

(defn solve
  "This unifies an existentail to a monotype"
  [ctx t-var-name typ]
  (assert (monotype? typ) "Can only solve for monotypes -- forgot a guard?")
  (let [[ctx-l ctx-r] (ctx-break ctx {:c-op :c-exists :c-var-name t-var-name})]
    (if (type-wf ctx-l typ) ;; Q: What does this check represent?
      (do (prn "solve: " [t-var-name typ "->" (c-exists-solved t-var-name typ)])
          {:solved  (ctx-concat ctx-l [(c-exists-solved t-var-name typ)] ctx-r)})
      {:unsolved true})))

(defmulti free-t-vars :t-op)
(defmethod free-t-vars :t-unit [_] #{})
(defmethod free-t-vars :t-var [typ] #{(:t-var-name typ)})
(defmethod free-t-vars :t-exists [typ] #{(:t-var-name typ)})
(defmethod free-t-vars :t-forall [typ] (set/difference (free-t-vars (:t-ret typ))
                                                       #{(:t-var-name typ)}))
(defmethod free-t-vars :t-fn [typ] (set/union (free-t-vars (:t-param typ))
                                              (free-t-vars (:t-ret typ))))

(defn ordered?
  "b occurs after a in ctx"
  [ctx t-var-name-a t-var-name-b]
  (let [ctx-l (ctx-drop ctx (c-exists t-var-name-b))]
    (contains? (existentials ctx-l) t-var-name-a)))

(defmulti rename-var
  "a la substitution: [new-name / for-name]expr
  This assumes analysis has already freshly renamed all variables.
  for-name is the actual symbol name to rebind (not the analyzed local var form)"
  (fn [new-name for-name expr] (:op expr)) )
(defmethod rename-var :const
  [new-name for-name expr] expr)
(defmethod rename-var :with-meta
  [new-name for-name expr]
  (update-in expr [:expr] #(rename-var new-name for-name %)))
(defmethod rename-var :annotation
  [new-name for-name expr]
  (update-in expr [:expr] #(rename-var new-name for-name %)))
(defmethod rename-var :do
  [new-name for-name expr]
  (-> (<<- (update-in expr [:statements]) (fn [ss])
           (vec) (for [s ss])
           (rename-var new-name for-name s))
      (update-in [:ret] #(rename-var new-name for-name %))))
(defmethod rename-var :invoke
  [new-name for-name expr]
  (-> (<<- (update-in expr [:args]) (fn [as])
           (vec) (for [a as])
           (rename-var new-name for-name a))
      (update-in [:fn] #(rename-var new-name for-name %))))
(defmethod rename-var :fn
  [new-name for-name expr]
  (<<- (update-in expr [:methods]) (fn [ms])
       (vec) (for [m ms])
       (update-in m [:body]) (fn [b])
       (rename-var new-name for-name b)))
(defmethod rename-var :local
  [new-name for-name expr]
  (if (= for-name (:name expr))
    (assoc expr :name new-name)
    expr))

;;; Not a multimethod since it's assumed the map-type should be you need to implement
(defn type-substitute
  "sub new-typ for t-var-name in typ"
  [new-typ t-var-name typ]
  (let [r (case (:t-op typ)
            :t-var (if (= t-var-name (:t-var-name typ)) new-typ typ)
            :t-exists (if (= t-var-name (:t-var-name typ)) new-typ typ)
            :t-forall (if (= t-var-name (:t-var-name typ))
                        (do (println "Should this ever happen with hygenic vars??") typ)
                        (update-in typ [:t-ret] #(type-substitute new-typ t-var-name %)))
            (map-type #(type-substitute new-typ t-var-name %) typ))]
    #_(prn "type-substitute" [new-typ t-var-name typ "->" r])
    r))

(declare subtype typesynth typesynth-invoke)

(defn typecheck
  "returns updated ctx"
  [ctx expr typ]
  (assert (vector? ctx))
  (let [r (cond
            (= :with-meta (:op expr)) (typecheck ctx (:expr expr) typ)
            (= :do (:op expr)) (typecheck ctx (:ret expr) typ)
            (and (= :const (:op expr))
                 (= nil (:val expr))
                 (= :t-unit (:t-op typ))) ctx
            (and (= :fn (:op expr))
                 (= :t-fn (:t-op typ)))
            , (do (assert (= :t-fn (:t-op typ)) (str "type isn't fn type " {:typ typ}))
                  (assert (= 1 (count (:methods expr))) "only single-arity methods supported")
                  (assert (= 1 (count (:params (first (:methods expr))))) "only single argument supported")
                  (let [param-name (:name (first (:params (first (:methods expr)))))
                        ctx-var-name (gensym param-name) ; Since param-name is gensymmed, I'm guessing we can just use the existing one and avoid the renaming?
                        ctx-elem {:c-op :c-var
                                  :c-var-name ctx-var-name
                                  :c-typ (:t-param typ)}]
                    (-> (typecheck (ctx-conj ctx ctx-elem)
                                   (rename-var ctx-var-name param-name (:body (first (:methods expr))))
                                   (:t-ret typ))
                        (ctx-drop ctx-elem))))
            (= :t-forall (:t-op typ))
            , (let [fresh (gensym (:t-var-name typ))
                    ctx-elem {:c-op :c-forall
                              :c-var-name fresh}]
                (-> (typecheck (ctx-conj ctx ctx-elem)
                               expr
                               (type-substitute {:t-op :t-var :t-var-name fresh}
                                                (:t-var-name typ)
                                                (:t-ret typ)))
                    (ctx-drop ctx-elem)))
            :else (let [{typ' :type ctx' :ctx} (typesynth ctx expr)]
                    (prn "synthed: " {:type typ' :ctx ctx'})
                    (subtype ctx' (type-apply ctx' typ') (type-apply ctx' typ))))]
    (prn "typechecked" (:op expr) [{:ctx ctx} expr typ "->" r])
    r))

(defmulti typesynth (fn [ctx expr] (:op expr)))
(defmethod typesynth :const [ctx expr]
  (if (= (:val expr) nil)
    {:type {:t-op :t-unit} :ctx ctx}
    (throw (ex-info "Can't synth type for " expr))))
(defmethod typesynth :local [ctx expr]
  (if-let [typ (find-var-type ctx (:name expr))] ;; (fn and let vars are both :local) - those bound by the env are inlined it seems? (why would these be and not let-bounds vars?
    {:type typ :ctx ctx}
    (throw (ex-info "var not found in context" {:ctx ctx :expr expr}))))
(defmethod typesynth :with-meta [ctx expr] (typesynth ctx (:expr expr)))
(defmethod typesynth :annotation [ctx expr]
  {:type (:type expr) :ctx (typecheck ctx (:expr expr) (:type expr))})
(defmethod typesynth :fn [ctx expr]
  (assert (= 1 (count (:methods expr))) "only single-arity methods supported")
  (assert (= 1 (count (:params (first (:methods expr))))) "only single argument supported")
  (let [param-name (:name (first (:params (first (:methods expr)))))
        ctx-var-name (gensym param-name) ; Since param-name is gensymmed, I'm guessing we can just use the existing one and avoid the renaming?
        exists-param (gensym (str "e-" param-name))
        exists-ret (gensym "ret")
        c-mk (c-marker exists-param)
        ctx-var {:c-op :c-var
                 :c-var-name ctx-var-name
                 :c-typ {:t-op :t-exists
                         :t-var-name exists-param}}
        [ctx-l ctx-r]
        , (-> (typecheck (ctx-concat ctx [c-mk
                                          (c-exists exists-param)
                                          (c-exists exists-ret)
                                          ctx-var])
                         (rename-var ctx-var-name param-name (:body (first (:methods expr))))
                         {:t-op :t-exists
                          :t-var-name exists-ret})
              (ctx-break c-mk))
        typ (type-apply ctx-r {:t-op :t-fn
                               :t-param {:t-op :t-exists
                                         :t-var-name exists-param}
                               :t-ret {:t-op :t-exists
                                       :t-var-name exists-ret}})
        evars (unsolved ctx-r) ;; I think this is becomes a big multi-var forall?
        freshes (repeatedly (count evars) #(gensym "freshes"))
        typ' (reduce (fn [t [f ev]]
                       (type-substitute {:t-op :t-var :t-var-name f} (:c-var-name ev) typ))
                     typ
                     (map vector freshes evars))
        typ'' (reduce (fn [t f] {:t-op :t-forall
                                 :t-var-name f
                                 :t-ret t})
                      typ'
                      freshes)]
    {:type typ''
     :ctx ctx-l}))
(defmethod typesynth :invoke [ctx expr]
  (let [{typ :type ctx' :ctx} (typesynth ctx (:fn expr))]
    (assert (= 1 (count (:args expr))) "only supports single arguments right now")
    (typesynth-invoke ctx' (type-apply ctx' typ) (first (:args expr)))))

(defn typesynth-invoke
  "type checks the actual argument of an invocation, given the type of the function."
  [ctx typ expr]
  (assert (vector? ctx))
  (case (:t-op typ)
    :with-meta (typesynth-invoke ctx typ (:expr expr))
    :t-forall (let [g (gensym "invokeforall")]
                (typesynth-invoke (ctx-conj ctx {:c-op :c-exists :c-var-name g})
                                  (type-substitute {:t-op :t-exists :t-var-name g}
                                                   (:t-var-name typ)
                                                   (:t-ret typ))
                                  expr))
    :t-exists (let [garg (gensym "invoke-exarg") ;; refining our knowledge of an existential variable
                    gret (gensym "invoke-gret")
                    [ctx-l ctx-r] (ctx-break ctx {:c-op :c-exists :c-var-name (:t-var-name typ)})
                    ctx' (typecheck (ctx-concat ctx-l
                                                [{:c-op :c-exists :c-var-name garg}
                                                 {:c-op :c-exists :c-var-name gret}
                                                 {:c-op :c-exists-solved
                                                  :c-var-name (:t-var-name typ)
                                                  :c-typ {:t-op :t-fn
                                                          :t-param {:t-op :t-exists :t-var-name garg}
                                                          :t-ret {:t-op :t-exists :t-var-name gret}}}]
                                                ctx-r)
                                    expr
                                    {:t-op :t-exists :t-var-name garg})]
                {:type {:t-op :t-exists :t-var-name gret}
                 :ctx ctx'})
    :t-fn (let [ctx' (typecheck ctx expr (:t-param typ))]
            {:type (:t-ret typ)
             :ctx ctx'})
    (throw (ex-info "Can't check this invoke" {:ctx ctx :typ typ :expr expr}))))

(defn flip [dir]
  (case dir :left :right :right :left))

(declare instantiate-poly)
(defn instantiate
  "returns a context.
  direction is which side of < the existential is on that we're trying to instantiate."
  [ctx t-var-name dir typ]
  (prn "instantiate-l" [ctx t-var-name typ])
  (if-let [ctx' (:solved (and (monotype? typ)
                              (solve ctx t-var-name typ)))]
    ctx'
    (instantiate-poly ctx t-var-name dir typ)))

(defmulti instantiate-poly
  "Called for types where monotype? has returned false."
  (fn [ctx t-var-name dir typ] (:t-op typ)))

(defmethod instantiate-poly :t-exists
  [ctx t-var-name dir typ]
  (if (ordered? ctx t-var-name (:t-var-name typ)) ;; I guess this has to succeed? This seems to just be careful control over the ctx order.
    (:solved (solve ctx (:t-var-name typ) {:t-op :t-exists
                                           :t-var-name t-var-name}))
    (do (throw (ex-info "NOTE: Weird case hit:" {:t-var-name t-var-name :typ typ}))
        (:solved (solve ctx t-var-name typ)))))

(defmethod instantiate-poly :t-fn
  [ctx t-var-name dir typ]
  (let [param' (gensym)
        ret' (gensym)
        ctx' (instantiate
              (let [[ctx-l ctx-r] (ctx-break ctx (c-exists t-var-name))]
                (ctx-concat ctx-l
                            [(c-exists ret')
                             (c-exists param')
                             (c-exists-solved t-var-name {:t-op :t-fn
                                                          :t-param {:t-op :t-exists
                                                                    :t-var-name param'}
                                                          :t-ret {:t-op :t-exists
                                                                  :t-var-name ret'}})]
                            ctx-r))
              param'
              (flip dir)
              (:t-param typ))]
    (instantiate ctx' ret' dir (type-apply ctx' (:t-ret typ)))))

(defmethod instantiate-poly :t-forall
  [ctx t-var-name dir typ]
  (case dir
    :left
    , (let [var-name' (gensym)
            ctx-elem {:c-op :c-forall
                      :c-var-name var-name'}]
        (-> (instantiate (ctx-concat ctx [ctx-elem]) ; Why wasn't this a ctx-conj? added to the other end?
                         t-var-name
                         :left
                         (type-substitute {:t-op :t-var ; Is this fresh renaming necessary?
                                           :t-var-name var-name'}
                                          (:t-var-name typ)
                                          (:t-ret typ)))
            (ctx-drop ctx-elem)))
    :right
    ,  (let [var-name' (gensym) ; This one is the difference! it flips the forall to an existential!.
             ctx-marker (c-marker var-name')
             ctx-elem (c-exists-solved var-name')]
         (-> (instantiate (ctx-concat ctx [ctx-marker ctx-elem]) ; Why wasn't this a ctx-conj? added to the other end?
                          t-var-name
                          :right
                          (type-substitute {:t-op :t-exists ; and replacing with an exists here instead of forall.
                                            :t-var-name var-name'}
                                           (:t-var-name typ)
                                           (:t-ret typ)))
             (ctx-drop ctx-marker)))))

(defmulti subtype
  "typ1 < typ2 - returns a new context"
  (fn [ctx typ1 typ2] [(:t-op typ1) (:t-op typ2)]))

(defmethod subtype [:t-unit :t-unit]
  [ctx typ1 typ2]
  ctx)

(defmethod subtype [:t-var :t-var]
  [ctx typ1 typ2]
  (if (= (:t-var-name typ1) (:t-var-name typ1))
    ctx
    (throw (ex-info "Vars don't match" {:ctx ctx :t1 typ1 :t2 typ2}))))

(defmethod subtype [:t-fn :t-fn]
  [ctx typ1 typ2]
  (let [ctx' (subtype ctx (:t-param typ2) (:t-param typ1))] ; Note polarity swap!
    (subtype ctx' (type-apply ctx' (:t-ret typ1))  (type-apply ctx' (:t-ret typ2)))))

(defmethod subtype :default
  [ctx typ1 typ2]
  (cond
    (= :t-forall (:t-op typ2)) (let [var-name' (gensym "subtype-r")
                                     ctx-elem {:c-op :c-forall
                                               :c-var-name var-name'}]
                                 (-> (subtype (ctx-concat ctx [ctx-elem])
                                              typ1
                                              (type-substitute {:t-op :t-var
                                                                :t-var-name var-name'}
                                                               (:t-var-name typ2)
                                                               (:t-ret typ2)))
                                     (ctx-drop ctx-elem)))
    (= :t-forall (:t-op typ1)) (let [var-name' (gensym "subtype-l")]
                                 (-> (subtype (ctx-concat ctx [(c-marker var-name')
                                                               {:c-op :c-exists
                                                                :c-var-name var-name'}])
                                              (type-substitute {:t-op :t-exists
                                                                :t-var-name var-name'}
                                                               (:t-var-name typ1)
                                                               (:t-ret typ1))
                                              typ2)
                                     (ctx-drop (c-marker var-name'))))
    (and (= :t-exists (:t-op typ1))
         (= :t-exists (:t-op typ2))
         (= (:t-var-name typ1) (:t-var-name typ2))
         (contains? (existentials ctx) (:t-var-name typ1)))
    , ctx
    (and (= :t-exists (:t-op typ1))
         (contains? (existentials ctx) (:t-var-name typ1))
         (not (contains? (free-t-vars typ2) (:t-var-name typ1))))
    , (instantiate ctx (:t-var-name typ1) :left typ2)
    (and (= :t-exists (:t-op typ2))
         (contains? (existentials ctx) (:t-var-name typ2))
         (not (contains? (free-t-vars typ1) (:t-var-name typ2))))
    , (instantiate ctx (:t-var-name typ2) :right typ1)
    :else (throw (ex-info "No matching clause" {:ctx ctx :t1 typ1 :t2 typ2}))))

;;;;;;;;; Scratch ;;;;;;;;;

(def builtin-env
  (-> (taj/empty-env)
      (assoc `annotations ::annotation))) ;; This doesn't seem to work, just defining it for real seems to work though.

(def sample-env
  (assoc (taj/empty-env)
         :locals {'fun1 (taem/elide-meta (taj/analyze+eval '(fn [x] x) (taj/empty-env)))}))

(defn infer
  [code]
  (let [ana (-> (taj/analyze+eval code (taj/empty-env))
                (analyze-annotations))
        {:keys [ctx type]} (typesynth [] ana)]
    (-> (type-apply ctx type)
        (renumber-varnames))))

(defn check
  "returns context if code typechecks"
  [code typ]
  (let [ana (-> (taj/analyze+eval code (taj/empty-env))
                (analyze-annotations))]
    (typecheck [] ana typ)))

#_(taj/analyze+eval '(+ 1 2) (taj/empty-env))

(def test-code '((fn [x] x) nil))
