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

(defn c-var-name-break
  "returns [ctx-left ctx-right]"
  [ctx c-var-name]
  (let [idx (ffirst (filter (fn [[i e]] (if (= (:c-var-name e) c-var-name) i nil)) (map-indexed vector ctx)))]
    (if (nil? idx) (throw (ex-info "Can't find element to break" {:ctx ctx :ctx-elem c-var-name}))
        [(subvec ctx 0 idx)
         (subvec ctx (inc idx) (count ctx))])))

(defn c-update-var
  "returns updated ctx"
  [ctx c-var-name f]
  (let [idx (ffirst (filter (fn [[i e]] (if (= (:c-var-name e) c-var-name) i nil)) (map-indexed vector ctx)))]
    (if (nil? idx) (throw (ex-info "Can't find element to break" {:ctx ctx :ctx-elem c-var-name}))
        (update-in ctx [idx] f))))

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

(defn c-find-var
  "Looks up a var in context"
  [ctx var-name]
  (first (filter (fn [e] (= (:c-var-name e) var-name)) ctx)))

(defn find-var-type ;; Context.hs
  "Looks up a var in context - returns its type or nil"
  [ctx var-name]
  (:c-typ (first (filter (fn [e] (= (:c-var-name e) var-name)) ctx))))

(defn existentials
  "returns a set of the existential var names"
  [ctx]
  (into #{} (map :c-var-name (filter #(#{:c-exists :c-exists-solved} (:c-op %)) ctx))))

(defmulti type-wf (fn [ctx typ] (:t-op typ)))

(defmethod type-wf ::t-var [ctx typ]
  (contains? (into #{} (map :c-var-name (filter #(= :c-forall (:c-op %)) ctx)))
             (:t-var-name typ)))
(defmethod type-wf ::t-forall [ctx typ]
  (type-wf (ctx-conj ctx {:c-op :c-forall :c-var-name (:t-var-name typ)})
           (:t-ret typ)))
(defmethod type-wf ::t-exists [ctx typ]
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
(defmethod map-type ::t-var    [f t] t)
(defmethod map-type ::t-forall [f t] (update-keys t [:t-ret] f))

(defn update-type
  "arg flipped map-type"
  [t f] (map-type f t))

(defn type-apply ;; apply Context.hs
  "looks up a type with the solved existentals replaced with what they're solved with?
   takes a type and returns a type."
  [ctx typ]
  (if (= ::t-exists (:t-op typ))
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
                ::t-forall
                (->> (assoc-in typ [:t-var-name] (fresh typ))
                     (map-type renumber))
                ::t-exists (if-let [new-name (get @env (:t-var-name typ))] ;; existentials implicitly range over entire expression
                            (assoc-in typ [:t-var-name] new-name)
                            (assoc-in typ [:t-var-name] (fresh typ)))
                ::t-var (if-let [new-name (get @env (:t-var-name typ))]
                         (assoc-in typ [:t-var-name] new-name)
                         (throw (ex-info "No name provided for var " {:typ typ})))
                (map-type renumber typ)))]
      (renumber typ))))

;; for ad-hoc hijaking of houw analysis works.
(defn analyze-annotations
  [expr]
  (cond
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

(defn t-exists
  [t-var-name]
  {:t-op ::t-exists
   :t-var-name t-var-name})

(defmulti monotype? :t-op)
(defmethod monotype? ::t-var  [_] true)
(defmethod monotype? ::t-exists [_] true)
(defmethod monotype? ::t-forall [_] false)


(defn solve
  "This unifies an existential to a monotype"
  [ctx t-var-name typ]
  (assert (monotype? typ) "Can only solve for monotypes -- forgot a guard?")
  (let [[ctx-l ctx-r] (ctx-break ctx {:c-op :c-exists :c-var-name t-var-name})]
    (if (type-wf ctx-l typ) ;; Q: What does this check represent?
      (do (prn "solve: " [t-var-name typ "->" (c-exists-solved t-var-name typ)])
          {:solved  (ctx-concat ctx-l [(c-exists-solved t-var-name typ)] ctx-r)})
      {:unsolved true})))

(defmulti free-t-vars :t-op)
(defmethod free-t-vars ::t-var [typ] #{(:t-var-name typ)})
(defmethod free-t-vars ::t-exists [typ] #{(:t-var-name typ)})
(defmethod free-t-vars ::t-forall [typ] (set/difference (free-t-vars (:t-ret typ))
                                                       #{(:t-var-name typ)}))

(defn ordered?
  "b occurs after a in ctx"
  [ctx t-var-name-a t-var-name-b]
  (let [ctx-l (ctx-drop ctx (c-exists t-var-name-b))]
    (contains? (existentials ctx-l) t-var-name-a)))

(defn operator
  "treat const values (like `nil`) as different operators than the analyzer does."
  [expr] (let [r (if (= :const (:op expr)) (:type expr) (:op expr))]
           (when (nil? r) (throw (ex-info "Nil opertator:" {:expr expr})))
           r))

(defmulti rename-var
  "a la substitution: [new-name / for-name]expr
  This assumes analysis has already freshly renamed all variables.
  for-name is the actual symbol name to rebind (not the analyzed local var form)"
  (fn [new-name for-name expr] (operator expr)))
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
(defmethod rename-var :local
  [new-name for-name expr]
  (if (= for-name (:name expr))
    (assoc expr :name new-name)
    expr))
(defmethod rename-var :invoke
  [new-name for-name expr]
  (-> (<<- (update-in expr [:args]) (fn [as])
           (vec) (for [a as])
           (rename-var new-name for-name a))
      (update-in [:fn] #(rename-var new-name for-name %))))

;;; Not a multimethod since it's assumed the map-type should be you need to implement
(defn type-substitute
  "sub new-typ for t-var-name in typ"
  [new-typ t-var-name typ]
  (let [r (case (:t-op typ)
            ::t-var    (if (= t-var-name (:t-var-name typ)) new-typ typ)
            ::t-exists (if (= t-var-name (:t-var-name typ)) new-typ typ)
            ::t-forall (if (= t-var-name (:t-var-name typ))
                         (do (println "Should this ever happen with hygenic vars??") typ)
                         (update-in typ [:t-ret] #(type-substitute new-typ t-var-name %)))
            (map-type #(type-substitute new-typ t-var-name %) typ))]
    #_(prn "type-substitute" [new-typ t-var-name typ "->" r])
    r))

(declare subtype typesynth typecheck)

(derive ::t-exists ::t-any-type)
(derive ::t-forall ::t-any-type)
(derive ::t-var    ::t-any-type)

;; returns a context
(defmulti typecheck (fn [ctx expr typ] (prn "typecheck:" [ctx expr typ]) [(operator expr) (:t-op typ)]))

(defmethod typecheck [:with-meta ::t-any-type]
  [ctx expr typ]
  (typecheck ctx (:expr expr) typ))

(defmethod typecheck [:do ::t-any-type]
  [ctx expr typ]
  (typecheck ctx (:ret expr) typ))

(defmethod typecheck :default
  [ctx expr typ]
  (cond
    (= ::t-forall (:t-op typ))
    , (let [fresh (gensym (:t-var-name typ))
            ctx-elem {:c-op :c-forall
                      :c-var-name fresh}]
        (-> (typecheck (ctx-conj ctx ctx-elem)
                       expr
                       (type-substitute {:t-op ::t-var :t-var-name fresh}
                                        (:t-var-name typ)
                                        (:t-ret typ)))
            (ctx-drop ctx-elem)))
    :else (let [{typ' :type ctx' :ctx} (do "Giving up" (typesynth ctx expr))]
            (prn "synthed: " {:type typ' :ctx ctx'})
            (subtype ctx' (type-apply ctx' typ') (type-apply ctx' typ)))))

;; Let anybody hijack invoke expressions using specific fn vars to dispatch.
(defmulti typesynth-invoke (fn [ctx expr] (let [v (get-in expr [:fn :var])]
                                            (if (var? v)
                                              (symbol (-> v .ns .name name)
                                                      (-> v .sym name))
                                              nil))))

(defmethod typesynth-invoke 'bidirectional.bidirectional/ann
  [ctx expr]
  (assert (= 2 (count (:args expr))) "annotation should have two arguments: (ann expr type)")
  (assert (:literal? (second (:args expr))) "second argument to ann must be a type literal")
  (let [anned-expr  (first (:args expr))
        typ (:val (second (:args expr)))]
    {:type typ :ctx (typecheck ctx anned-expr typ)}))

;; Returns {:type typ :ctx ctx}
(defmulti typesynth (fn [ctx expr] (prn "typesynth" [ctx expr]) (operator expr)))
(defmethod typesynth :local [ctx expr]
  (if-let [typ (find-var-type ctx (:name expr))] ;; (fn and let vars are both :local) - those bound by the env are inlined it seems? (why would these be and not let-bounds vars?
    {:type typ :ctx ctx}
    (throw (ex-info "var not found in context" {:ctx ctx :expr expr}))))
(defmethod typesynth :with-meta [ctx expr] (typesynth ctx (:expr expr)))
(defmethod typesynth :invoke [ctx expr] (typesynth-invoke ctx expr))



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

(defmethod instantiate-poly ::t-exists
  [ctx t-var-name dir typ]
  (if (ordered? ctx t-var-name (:t-var-name typ)) ;; I guess this has to succeed? This seems to just be careful control over the ctx order.
    (:solved (solve ctx (:t-var-name typ) {:t-op ::t-exists
                                           :t-var-name t-var-name}))
    (do (throw (ex-info "Weird case hit (this should have been handled by the first call to instantiate?):"
                        {:t-var-name t-var-name :typ typ}))
        #_(:solved (solve ctx t-var-name typ)))))



(defmethod instantiate-poly ::t-forall
  [ctx t-var-name dir typ]
  (case dir
    :left
    , (let [var-name' (gensym)
            ctx-elem {:c-op :c-forall
                      :c-var-name var-name'}]
        (-> (instantiate (ctx-concat ctx [ctx-elem]) ; Why wasn't this a ctx-conj? added to the other end?
                         t-var-name
                         :left
                         (type-substitute {:t-op ::t-var ; Is this fresh renaming necessary?
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
                          (type-substitute {:t-op ::t-exists ; and replacing with an exists here instead of forall.
                                            :t-var-name var-name'}
                                           (:t-var-name typ)
                                           (:t-ret typ)))
             (ctx-drop ctx-marker)))))

(defmulti subtype
  "typ1 < typ2 - returns a new context"
  (fn [ctx typ1 typ2] [(:t-op typ1) (:t-op typ2)]))

(defmethod subtype [::t-var ::t-var]
  [ctx typ1 typ2]
  (if (= (:t-var-name typ1) (:t-var-name typ1))
    ctx
    (throw (ex-info "Vars don't match" {:ctx ctx :t1 typ1 :t2 typ2}))))

(defmethod subtype :default
  [ctx typ1 typ2]
  (cond
    (= ::t-forall (:t-op typ2)) (let [var-name' (gensym "subtype-r")
                                      ctx-elem {:c-op :c-forall
                                                :c-var-name var-name'}]
                                  (-> (subtype (ctx-concat ctx [ctx-elem])
                                               typ1
                                               (type-substitute {:t-op ::t-var
                                                                 :t-var-name var-name'}
                                                                (:t-var-name typ2)
                                                                (:t-ret typ2)))
                                      (ctx-drop ctx-elem)))
    (= ::t-forall (:t-op typ1)) (let [var-name' (gensym "subtype-l")]
                                  (-> (subtype (ctx-concat ctx [(c-marker var-name')
                                                                {:c-op :c-exists
                                                                 :c-var-name var-name'}])
                                               (type-substitute {:t-op ::t-exists
                                                                 :t-var-name var-name'}
                                                                (:t-var-name typ1)
                                                                (:t-ret typ1))
                                               typ2)
                                      (ctx-drop (c-marker var-name'))))
    (and (= ::t-exists (:t-op typ1))
         (= ::t-exists (:t-op typ2))
         (= (:t-var-name typ1) (:t-var-name typ2))
         (contains? (existentials ctx) (:t-var-name typ1)))
    , ctx
    (and (= ::t-exists (:t-op typ1))
         (contains? (existentials ctx) (:t-var-name typ1))
         (not (contains? (free-t-vars typ2) (:t-var-name typ1))))
    , (instantiate ctx (:t-var-name typ1) :left typ2)
    (and (= ::t-exists (:t-op typ2))
         (contains? (existentials ctx) (:t-var-name typ2))
         (not (contains? (free-t-vars typ1) (:t-var-name typ2))))
    , (instantiate ctx (:t-var-name typ2) :right typ1)
    :else (throw (ex-info "Type error. t1 is not a subtype of t2" {:ctx ctx :t1 typ1 :t2 typ2}))))

;;;;;;;;; Scratch ;;;;;;;;;

(def builtin-env
  (-> (taj/empty-env)
      (assoc `annotations ::annotation))) ;; This doesn't seem to work, just defining it for real seems to work though.

(def sample-env
  (assoc (taj/empty-env)
         :locals {'fun1 (taem/elide-meta (taj/analyze+eval '(fn [x] x) (taj/empty-env)))}))

(defn ctx-infer
  [code]
  (let [ana (-> (taj/analyze+eval code (taj/empty-env))
                (analyze-annotations))
        {:keys [ctx type]} (typesynth [] ana)]
    {:type (-> (type-apply ctx type)
               (renumber-varnames))
     :ctx ctx}))

(defn infer
  [code]
  (:type (ctx-infer code)))

(defn check
  "returns context if code typechecks"
  [code typ]
  (let [ana (-> (taj/analyze+eval code (taj/empty-env))
                (analyze-annotations))]
    (typecheck [] ana typ)))

#_(taj/analyze+eval '(+ 1 2) (taj/empty-env))

(def test-code '((fn [x] x) nil))
