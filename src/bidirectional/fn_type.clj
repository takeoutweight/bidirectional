(ns bidirectional.fn-type
  (:require [bidirectional.bidirectional :refer :all :as bi]
            [clojure.set :as set]))

(derive ::t-fn ::bi/t-any-type)

(defmethod type-wf ::t-fn [ctx typ]
  (and (type-wf ctx (:t-param typ))
       (type-wf ctx (:t-ret typ))))

(defmethod map-type ::t-fn     [f t] (update-keys t [:t-param :t-ret] f))

(defmethod monotype? ::t-fn [typ] (and (monotype? (:t-param typ))
                                      (monotype? (:t-ret typ))))

(defmethod free-t-vars ::t-fn [typ] (set/union (free-t-vars (:t-param typ))
                                              (free-t-vars (:t-ret typ))))

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
                 :c-typ {:t-op ::bi/t-exists
                         :t-var-name exists-param}}
        [ctx-l ctx-r]
        , (-> (typecheck (ctx-concat ctx [c-mk
                                          (c-exists exists-param)
                                          (c-exists exists-ret)
                                          ctx-var])
                         (rename-var ctx-var-name param-name (:body (first (:methods expr))))
                         {:t-op ::bi/t-exists
                          :t-var-name exists-ret})
              (ctx-break c-mk))
        typ (type-apply ctx-r {:t-op ::t-fn
                               :t-param {:t-op ::bi/t-exists
                                         :t-var-name exists-param}
                               :t-ret {:t-op ::bi/t-exists
                                       :t-var-name exists-ret}})
        evars (unsolved ctx-r) ;; I think this is becomes a big multi-var forall?
        freshes (repeatedly (count evars) #(gensym "freshes"))
        typ' (reduce (fn [t [f ev]]
                       (type-substitute {:t-op ::bi/t-var :t-var-name f} (:c-var-name ev) typ))
                     typ
                     (map vector freshes evars))
        typ'' (reduce (fn [t f] {:t-op ::bi/t-forall
                                 :t-var-name f
                                 :t-ret t})
                      typ'
                      freshes)]
    {:type typ''
     :ctx ctx-l}))

(defmethod instantiate-poly ::t-fn
  [ctx t-var-name dir typ]
  (let [param' (gensym)
        ret' (gensym)
        ctx' (instantiate
              (let [[ctx-l ctx-r] (ctx-break ctx (c-exists t-var-name))]
                (ctx-concat ctx-l
                            [(c-exists ret')
                             (c-exists param')
                             (c-exists-solved t-var-name {:t-op ::t-fn
                                                          :t-param {:t-op ::bi/t-exists
                                                                    :t-var-name param'}
                                                          :t-ret {:t-op ::bi/t-exists
                                                                  :t-var-name ret'}})]
                            ctx-r))
              param'
              (flip dir)
              (:t-param typ))]
    (instantiate ctx' ret' dir (type-apply ctx' (:t-ret typ)))))

(defmethod subtype [::t-fn ::t-fn]
  [ctx typ1 typ2]
  (let [ctx' (subtype ctx (:t-param typ2) (:t-param typ1))] ; Note polarity swap!
    (subtype ctx' (type-apply ctx' (:t-ret typ1))  (type-apply ctx' (:t-ret typ2)))))

(defmethod typecheck-m [:fn ::t-fn]
  [ctx expr typ]
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
