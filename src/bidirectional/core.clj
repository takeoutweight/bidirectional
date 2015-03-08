(ns bidirectional.core
  (:require [clojure.tools.analyzer :as ta]
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
  "TODO: Not sure this is right - if vecs and contexts can be interchangeable like this."
  [& ctxs]
  (vec (apply concat ctxs)))

(defn ctx-drop
  "I think this drops everything to the right of elem, including elem."
  [ctx ctx-elem]
  (throw (Exception. "TODO")))

(defn ctx-break
  "returns [ctx-left ctx-right]"
  [ctx ctx-elem]
  (throw (Exception. "TODO")))

(defn ctx-apply
  [ctx typ]
  (throw (Exception. "TODO")))

(defn type-wf
  [ctx typ]
  (throw (Exception. "TODO")))

(defn find-solved
  "returns nil or the solved monotype"
  [ctx var-name]
  (first (filter (fn [c-elem] (and (= :c-exists-solved (:c-op c-elem))
                                   (= var-name (:c-var-name c-elem))
                                   (:c-typ c-elem)))
                 ctx)))

(defn type-apply
  "??? Maybe looks up a type with the solved existentals replaced with what they're solved with?
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
    typ))

(defn c-exists
  "constructor"
  [c-var-name]
  {:c-op :c-exists :c-var-name c-var-name})

(defn c-exists-solved
  "constructor"
  [c-var-name typ]
  {:c-op :c-exists-solved :c-var-name c-var-name :c-typ typ})

(defn ordered?
  "b occurs after a in ctx"
  [ctx t-var-name-a t-var-name-b]
  (let [ctx-l (ctx-drop ctx (c-exists t-var-name-b))]
    (contains? (existentials ctx-l) t-var-name-a)))

(defn monotype?
  [typ]
  (throw (Exception. "TODO")))

(defn solve
  "TODO: this seems nedlessly complex if it's just a wf check?"
  [ctx t-var-name typ]
  (assert (monotype? typ) "Can only solve for monotypes -- forgot a guard?")
  (let [[ctx-l ctx-r] (ctx-break {:c-op :c-exists :c-var-name t-var-name} ctx)]
    (if (type-wf ctx-l typ) ;; Q: What does this check represent?
      {:solved  (ctx-concat ctx-l [(c-exists-solved t-var-name typ)] ctx-r)}
      {:unsolved true})))

(defn existentials
  "returns a set of the existential var names"
  [ctx]
  (throw (Exception. "TODO")))

(defn free-t-vars
  [ctx]
  (throw (Exception. "TODO")))

(defn rename-var
  "a var in expression form."
  [expr new-name]
  (assert (= (:op expr) :local) "tried to rename not-a-local var")
  (assoc-in expr :name new-name))

(def sample-env
  (assoc (taj/empty-env)
         :locals {'fun1 (taem/elide-meta (taj/analyze+eval '(fn [x] x) (taj/empty-env)))}))

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

(declare subtype typesynth)

(defn typecheck [ctx expr typ]
  (case (:op expr) ;; TODO Need to dispatch on expor on some (eg, is with-meta even checked at all? or synthed?) and typ on most?
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
    (let [{typ' :typ ctx' :ctx} (typesynth ctx expr)]
      (subtype ctx' (ctx-apply ctx' typ') (ctx-apply ctx' typ)))))

(defn typesynth [ctx expr]
  (case (:op expr)
    :with-meta (typesynth ctx (:expr expr))
    :fn :TODO))

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
    (case (:t-op typ)                   ; TODO some checkwftypes of return
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
                      ctx-marker {:c-op :c-marker
                                  :c-var-name var-name'}
                      ctx-elem {:c-op :c-exists
                                :c-var-name var-name'}]
                  (-> (instantiate-r (ctx-concat ctx [ctx-marker ctx-elem]) ; Why wasn't this a ctx-conj? added to the other end?
                                     (type-substitute {:t-op :t-exists ; and replacing with an exists here instead of forall.
                                                       :t-var-name var-name'}
                                                      (:t-var-name typ)
                                                      (:t-ret typ))
                                     t-var-name)
                      (ctx-drop ctx-marker))))))

(defn subtype
  "typ1 < typ2"
  [ctx typ1 typ2]
  (case [(:t-op typ1) (:t-op typ2)]
    [:t-var :t-var]
    [:t-fn :t-fn]
    [:t-exists :t-exists]
    (if (and (= :t-exists (:t-op typ1))
             (contains? (existentials ctx) (:t-var-name typ1))
             (not (contains? (free-t-vars typ2) (:t-var-name typ1))))
      (instantiate-l ))
    ))
