(ns bidirectional.core
  (:require [clojure.tools.analyzer :as ta]
            [clojure.set :as set]
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

(defn existentials
  "returns a set of the existential var names"
  [ctx]
  (into #{} (map :c-var-name (filter #(#{:c-exists :c-exists-solved} (:c-op %)) ctx))))

(defn type-wf ;; cf typewf Contex.hs
  "returns a boolean"
  [ctx typ]
  (case (:t-op typ)
    :t-var (contains? (into #{} (map :c-var-name (filter #(= :c-forall (:c-op %)) ctx)))
                      (:t-var-name typ))
    :t-fn (and (type-wf ctx (:t-param typ))
               (type-wf ctx (:t-param typ)))
    :t-forall (type-wf (ctx-conj ctx {:c-op :c-forall :c-var-name (:t-var-name typ)})
                       (:t-ret typ))
    :t-exists (contains? (existentials ctx)
                         (:t-var-name typ))))

(defn find-solved
  "returns nil or the solved monotype"
  [ctx var-name]
  (first (filter (fn [c-elem] (and (= :c-exists-solved (:c-op c-elem))
                                   (= var-name (:c-var-name c-elem))
                                   (:c-typ c-elem)))
                 ctx)))

(defn unsolved
  "returns set of unsolved existentials"
  [ctx]
  (into #{} (filter #(#{:c-exists} (:c-op %)) ctx)))

(defn type-apply ; apply Context.hs
  "looks up a type with the solved existentals replaced with what they're solved with?
   takes a type and returns a type."
  [ctx typ]
  (case (:t-op typ)
    :t-forall (update-in typ [:t-ret] #(type-apply ctx %))
    :t-fn (-> typ
              (update-in [:t-param] #(type-apply ctx %))
              (update-in [:t-ret] #(type-apply ctx %)))
    :t-exists (if-let [typ' (find-solved ctx (:t-var-name typ))]
                (type-apply ctx typ')
                typ)
    :t-var typ))

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

(defn monotype?
  [typ]
  (case (:t-op typ)
    :t-var true
    :t-exists true
    :t-forall false
    :t-fn (and (monotype? (:t-param typ))
               (monotype? (:t-ret typ)))))

(defn solve
  "this seems nedlessly complex if it's just a wf check?"
  [ctx t-var-name typ]
  (assert (monotype? typ) "Can only solve for monotypes -- forgot a guard?")
  (let [[ctx-l ctx-r] (ctx-break {:c-op :c-exists :c-var-name t-var-name} ctx)]
    (if (type-wf ctx-l typ) ;; Q: What does this check represent?
      {:solved  (ctx-concat ctx-l [(c-exists-solved t-var-name typ)] ctx-r)}
      {:unsolved true})))

(defn free-t-vars
  "returns the set of t-var-names that are free"
  [typ]
  (case (:t-op typ)
    :t-var #{(:t-var-name typ)}
    :t-exists #{(:t-var-name typ)}
    :t-forall (set/difference (free-t-vars (:t-ret typ)) #{(:t-var-name typ)})
    :t-fn (set/union (free-t-vars (:t-param typ))
                     (free-t-vars (:t-ret typ)))))

(defn ordered?
  "b occurs after a in ctx"
  [ctx t-var-name-a t-var-name-b]
  (let [ctx-l (ctx-drop ctx (c-exists t-var-name-b))]
    (contains? (existentials ctx-l) t-var-name-a)))

(defn rename-var
  "a la substitution: [new-name / for-name]expr
  This assumes analysis has already freshly renamed all variables.
  for-name is the actual symbol name to rebind (not the analyzed local var form)"
  [new-name for-name expr]
  (case (:op expr)
    :with-meta (update-in expr [:expr] #(rename-var new-name for-name %))
    :do (-> (<<- (update-in expr [:statements]) (fn [ss])
                 (vec) (for [s ss])
                 (rename-var new-name for-name s))
            (update-in [:ret] #(rename-var new-name for-name %)))
    :invoke (-> (<<- (update-in expr [:args]) (fn [as])
                     (vec) (for [a as])
                     (rename-var new-name for-name a))
                (update-in [:fn] #(rename-var new-name for-name %)))
    :fn (<<- (update-in expr [:methods]) (fn [ms])
             (vec) (for [m ms])
             (update-in m [:body]) (fn [b])
             (rename-var new-name for-name b))
    :local (if (= for-name (:name expr))
             (assoc expr :name new-name)
             expr)))

(defn type-substitute
  "sub new-typ for t-var-name in typ"
  [new-typ t-var-name typ]
  (case (:t-op typ)
    :t-var (if (= t-var-name (:t-var-name typ)) new-typ typ)
    :t-exists (if (= t-var-name (:t-var-name typ)) new-typ typ)
    :t-forall (if (= t-var-name (:t-var-name typ))
                (do (println "Should this ever happen with hygenic vars??") typ)
                (update-in typ [:t-ret] #(type-substitute new-typ t-var-name %)))
    :t-fn (-> typ
              (update-in typ [:t-param] #(type-substitute new-typ t-var-name %))
              (update-in typ [:t-ret] #(type-substitute new-typ t-var-name %)))))

(declare subtype typesynth typeapplysynth)

(defn typecheck [ctx expr typ]
  (case (:op expr)
    :with-meta (typecheck ctx (:expr expr) typ)
    :do (typecheck ctx (:ret expr) typ) ;; TODO synthesize non-return statements of a do? is do even checked?
    :fn (do (assert (= :t-fn (:t-op typ)) "type isn't fn type")
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
    ;; subtype - TODO: does this "else" work for us, even though we have a bigger :op space?
    (let [{typ' :type ctx' :ctx} (typesynth ctx expr)]
      (subtype ctx' (type-apply ctx' typ') (type-apply ctx' typ)))))

(defn typesynth
  "returns {:type t :ctx c}"
  [ctx expr]
  (case (:op expr)
    :var :TODO                          ; i.e. calling a named fn - synth vs check? both probably.
    :with-meta (typesynth ctx (:expr expr))
    :annotation {:type (:type expr) :ctx (typecheck ctx (:expr expr) (:type expr))} ; TODO This doesn't exist in source
    :fn (do (assert (= 1 (count (:methods expr))) "only single-arity methods supported")
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
                                 (type-substitute {:to-op :t-var :t-var-name f} (:c-var-name ev) typ))
                               typ
                               (map vector freshes evars))
                  typ'' (reduce (fn [t f] {:t-op :t-forall
                                           :t-var-name f
                                           :t-ret t})
                                typ'
                                freshes)]
              {:type typ''
               :ctx ctx-l}))
    :invoke (let [{typ :type ctx' :ctx} (typesynth ctx (:fn expr))]
              (assert (= 1 (count (:args expr))) "only supports single arguments right now")
              (typeapplysynth typ (type-apply ctx' typ) (first (:args expr))))))

(defn typeapplysynth
  "type checks the actual argument of an invocation, given the type of the function."
  [ctx typ expr]
  (case (:t-op typ)
    :with-meta (typeapplysynth ctx typ (:expr expr)) ;; TODO: should we normalize these away somehow? embed their meta into their :expr probably.
    :t-forall (let [g (gensym "invokeforall")]
                (typeapplysynth (ctx-conj ctx {:c-op :c-exists :c-var-name g})
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

(declare instantiate-r)
(defn instantiate-l
  "returns a context"
  [ctx t-var-name typ]
  (if-let [ctx' {:solved (and (monotype? typ)
                              (solve ctx t-var-name typ))}]
    ctx'
    (case (:t-op typ)
      :t-exists (if (ordered? ctx t-var-name (:t-var-name typ)) ;; I guess this has to succeed? This seems to just be careful control over the ctx order.
                  (:solved (solve ctx (:t-var-name typ) (c-exists t-var-name)))
                  (do (prn "NOTE: Weird case hit:") (:solved (solve ctx t-var-name typ)))) ;; Q: How would get to this case? Wouldn't it be hit in the "if" above?!
      :t-fn (let [param' (gensym)
                  ret' (gensym)
                  ctx' (instantiate-r
                        (let [[ctx-l ctx-r] (ctx-break ctx (c-exists t-var-name))]
                          (ctx-concat ctx-l
                                      [(c-exists ret')
                                       (c-exists param')
                                       (c-exists-solved t-var-name {:t-op :t-fn
                                                                    :t-param {:t-exists param'}
                                                                    :t-ret {:t-exists ret'}})]
                                      ctx-r))
                        (:t-param typ)
                        param')]
              (instantiate-l ctx' ret' (type-apply ctx' (:t-ret typ))))
      :t-forall (let [var-name' (gensym)
                      ctx-elem {:c-op :c-forall
                                :c-var-name var-name'}]
                  (-> (instantiate-l (ctx-concat ctx [ctx-elem]) ; Why wasn't this a ctx-conj? added to the other end?
                                     t-var-name
                                     (type-substitute {:t-op :t-var ; Is this fresh renaming necessary?
                                                       :t-var-name var-name'}
                                                      (:t-var-name typ)
                                                      (:t-ret typ)))
                      (ctx-drop ctx-elem))))))

(defn instantiate-r
  "Q: Why are the args flipped from instantiate-l on this one? is that important?"
  [ctx typ t-var-name]
  (if-let [ctx' {:solved (and (monotype? typ) ; same as before
                              (solve ctx t-var-name typ))}]
    ctx'
    (case (:t-op typ)
      :t-exists (if (ordered? ctx t-var-name (:t-var-name typ)) ; same
                  (:solved (solve ctx (:t-var-name typ) (c-exists t-var-name)))
                  (do (prn "NOTE: Weird case hit:") (:solved (solve ctx t-var-name typ))))
      :t-fn (let [param' (gensym)
                  ret' (gensym)
                  ctx' (instantiate-l   ;flipped but same logic?
                        (let [[ctx-l ctx-r] (ctx-break ctx (c-exists t-var-name))]
                          (ctx-concat ctx-l
                                      [(c-exists ret')
                                       (c-exists param')
                                       (c-exists-solved t-var-name {:t-op :t-fn
                                                                    :t-param {:t-exists param'}
                                                                    :t-ret {:t-exists ret'}})]
                                      ctx-r))
                        param'
                        (:t-param typ))]
              (instantiate-r ctx' (type-apply ctx' (:t-ret typ)) ret'))
      :t-forall (let [var-name' (gensym) ; This one is the difference! it flips the forall to an existential!.
                      ctx-marker (c-marker var-name')
                      ctx-elem (c-exists-solved var-name')]
                  (-> (instantiate-r (ctx-concat ctx [ctx-marker ctx-elem]) ; Why wasn't this a ctx-conj? added to the other end?
                                     (type-substitute {:t-op :t-exists ; and replacing with an exists here instead of forall.
                                                       :t-var-name var-name'}
                                                      (:t-var-name typ)
                                                      (:t-ret typ))
                                     t-var-name)
                      (ctx-drop ctx-marker))))))

(defn subtype
  "typ1 < typ2 - returns a new context"
  [ctx typ1 typ2]
  (let [err (fn [msg] (throw (ex-info msg {:v1 typ1 :v2 typ2})))]
    (case [(:t-op typ1) (:t-op typ2)]
      [:t-var :t-var] (if (= (:t-var-name typ1) (:t-var-name typ1)) ctx (err "Vars don't match"))
      [:t-fn :t-fn] (let [ctx' (subtype ctx (:t-param typ2) (:t-param typ1))] ; Note polarity swap!
                      (subtype ctx' (type-apply ctx' (:t-ret typ1) (:t-ret typ2))))
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
        , (instantiate-l ctx (:t-var-name typ1) typ2)
        (and (= :t-exists (:t-op typ2))
             (contains? (existentials ctx) (:t-var-name typ2))
             (not (contains? (free-t-vars typ1) (:t-var-name typ2))))
        , (instantiate-r ctx typ1 (:t-var-name typ2))))))

;;;;;;;;; Scratch ;;;;;;;;;

(def sample-env
  (assoc (taj/empty-env)
         :locals {'fun1 (taem/elide-meta (taj/analyze+eval '(fn [x] x) (taj/empty-env)))}))

#_(taj/analyze+eval '(+ 1 2) (taj/empty-env))
