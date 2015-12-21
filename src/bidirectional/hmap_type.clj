(ns bidirectional.hmap-type
  (:require [bidirectional.bidirectional :refer :all :as bi]
            [bidirectional.fn-type :as fn]
            [clojure.tools.analyzer.jvm :as taj]
            [clojure.set :as set])
  (:import clojure.lang.ExceptionInfo))

(derive ::t-hmap ::bi/t-any-type)

(defmethod type-wf ::t-hmap [ctx typ]
  (every? identity (for [[fld typ] (:t-fields typ)] (type-wf ctx typ))))

(defmethod map-type ::t-hmap [f t]
  (<<- (update-in t [:t-fields]) (fn [flds])
       (update-keys flds (keys flds) f)))

(defmethod monotype? ::t-hmap [typ]
  (every? monotype? (for [[fld typ] (:t-fields typ)] typ)))

(defmethod free-t-vars ::t-hmap [typ]
  (apply set/union
         (map free-t-vars (for [[fld typ] (:t-fields typ)] typ))))

(defmethod rename-var :map
  [new-name for-name expr]
  (if (= :const (:op expr)) ;; :op :const contains no variabls
    expr
    (<<- (update-in expr [:vals]) (fn [vals])
         (vec) (for [v vals])
         (rename-var new-name for-name v))))

(defn hmap-typ?
  [typ]
  (= ::t-hmap (:t-op typ)))

(defn hmap-exists?
  [typ]
  (= ::t-hmap-exists (:t-op typ)))

(defn hmap-nil?
  [typ]
  (= ::t-hmap-nil (:t-op typ)))

;; TODO unify approach to handling existentials of different sorts
(defn hmap-existentials
  "returns the free hmap-exists c-var-names in the context"
  [ctx]
  (->> ctx
       (filter #(#{::c-hmap-exists} (:c-op %)))
       (map :c-var-name)
       (into #{})))

;; TODO unify approach to handling existentials of different sorts
(defn hmap-ordered?
  "true if r doesn't occur to the left of l in the context"
  [ctx c-var-name-l c-var-name-r]
  (let [[ctx-l ctx-r] (c-var-name-break ctx c-var-name-l)]
    (not (contains? (hmap-existentials ctx-l) c-var-name-r))))

(defn hmap-apply
  "pulls together all the existential row constraints, as well as resolving actual existentials.
  returns the normalized type based on the context."
  [ctx typ]
  (let [typ (type-apply ctx typ)]
    (cond
      (hmap-typ?    typ)
      ,(if (hmap-nil? (:t-rest typ))
         typ
         (let [c-exts (loop [c-exts (c-find-var ctx (:t-var-name (:t-rest typ)))]
                        (if (= ::c-hmap-exists-solved (:c-op c-exts))
                          (recur (c-find-var ctx (:c-equal-to-var-name c-exts)))
                          c-exts))]
           (when (not-empty (set/intersection (set (keys (:c-fields c-exts)))
                                              (set (keys (:t-fields typ)))))
             (throw (ex-info "Not sure what to do when constraints redundantly talk about the same keys. Is it okay as long as they're coherent?" {:ctx ctx :typ typ})))
           {:t-op ::t-hmap
            :t-fields (merge (:t-fields typ) (:c-fields c-exts))
            :t-rest (if (:c-principal? c-exts)
                      {:t-op ::t-hmap-nil}
                      {:t-op ::t-exists
                       :t-var-name (:c-var-name c-exts)})}))
      (hmap-exists? typ) (throw (ex-info "TODO" {}))
      (hmap-nil? typ) typ)))

(defn refine-existential
  "returns updated ctx"
  [ctx hmap-exst key typ]
  (throw (ex-info "TODO" {})))

(defn nil-existential
  [ctx hmap-exst]
  (c-update-var ctx (:t-var-name hmap-exst)
                (fn [c-exst]
                  (when-not (= {} (:c-fields c-exst))
                    (throw (ex-info "Not sure about this case. hmap existential carries constraints?" {:ctx ctx :hmap-exst hmap-exst})))
                  (assoc c-exst :c-principal? true))))

(defn intersect-constraints
  "c-hmap-exists don't, themselves, have :rest fields so unlike subtype this
  only intersects the field constraints.

  returns {:ctx ctx :fields intersected-field-constraints}"
  [ctx c-hmap-exst-l c-hmap-exst-r]
  (let [allkeys (set (concat (keys (:c-fields c-hmap-exst-l))
                             (keys (:c-fields c-hmap-exst-r))))
        ret
        ,(reduce (fn [{ctx :ctx fields :fields} key]
                   (let [left-t  (get key (:c-fields c-hmap-exst-l))
                         right-t (get key (:c-fields c-hmap-exst-r))]
                     (cond
                       ;; normal case
                       (and left-t right-t)
                       ,(try {:ctx (subtype ctx left-t right-t) :fields (assoc fields key left-t)}
                             (catch ExceptionInfo e
                               {:ctx (subtype ctx right-t left-t) :fields (assoc fields key right-t)}))
                       (and left-t (nil? right-t) (not (:c-principal? c-hmap-exst-r)))
                       ,{:ctx ctx :fields (assoc fields key left-t)}
                       (and right-t (nil? left-t) (not (:c-principal? c-hmap-exst-l)))
                       ,{:ctx ctx :fields (assoc fields key right-t)}
                       :else (throw (ex-info "Can't intersect hmap field constraint" {:ctx ctx :key key :c-hmap-exst-l c-hmap-exst-l :c-hmap-exst-r c-hmap-exst-r})))))
                 {:ctx ctx :fields {}}
                 allkeys)]
    (assoc ret :principal? (or (:c-principal? c-hmap-exst-l)
                               (:c-principal? c-hmap-exst-r)))))

(defn unify-existential
  "returns updated context"
  [ctx hmap-exst-1 hmap-exst-2]
  (let [{ctx :ctx fields :fields principal? :principal?}
        ,(intersect-constraints ctx hmap-exst-1 hmap-exst-2)
        [hmap-exst-l hmap-exst-r] (if (hmap-ordered? (:c-var-name hmap-exst-1) (:c-var-name hmap-exst-2))
                                    [hmap-exst-1 hmap-exst-2]
                                    [hmap-exst-2 hmap-exst-1])
        ctx (c-update-var ctx (:c-var-name hmap-exst-r)
                          (fn [_]
                            {:c-op ::c-hmap-exists-solved
                             :c-var-name (:c-var-name hmap-exst-r)
                             :c-equal-to-var-name (:c-var-name hmap-exst-l)}))
        ctx (c-update-var ctx (:c-var-name hmap-exst-l)
                          (fn [c-elem]
                            (-> c-elem
                                (assoc :c-fields fields)
                                (assoc :c-principal? principal?))))]
    ctx))

;;; Not sure the best way to normalize between :op :map and :op :const :type :map
(defn unconst-map
  "Analyzes a :op :const map one more level into the keys and values."
  [expr]
  (if (= :const (:op expr))
    (-> expr
        (assoc :op :map)
        (assoc :vals (vec (map #(taj/analyze+eval % (taj/empty-env)) (vals (:val expr)))))
        (assoc :keys (vec (map #(taj/analyze+eval % (taj/empty-env)) (keys (:val expr))))))
    expr))

(defmethod typesynth :map [ctx expr]
  (let [expr (unconst-map expr)
        [ctx fields] (reduce (fn [[ctx fields] [k v]]
                               (when-not (= :keyword (:type k))
                                 (throw (ex-info "Non-keywords can't be used as HMap keys" {:ctx ctx :k k})))
                               (let [{:keys [ctx type]} (typesynth ctx v)]
                                 [ctx (assoc fields (:val k) type)]))
                             [ctx {}]
                             (map vector (:keys expr) (:vals expr)))]
    {:type {:t-op ::t-hmap
            :t-fields fields
            :t-rest {:t-op ::t-hmap-nil}}
     :ctx ctx}))

#_
(defmethod typecheck [:map ::t-hmap]
  [ctx expr typ]
  (let [expr (unconst-map expr)
        expr-map (into {} (map vector (map :val (:keys expr)) (:vals expr)))
        ctx (reduce (fn [ctx [k v]]
                      (typecheck ctx (get expr-map k) v))
                    ctx
                    (:t-fields typ))]
    ctx))

;; TODO This probably won't play nice with keywords as just raw enum values?
;; besides, we have :keyword-invoke as a distinguished form
(defmethod typesynth :keyword [ctx expr]
  (let [exists-ret (gensym (:val expr))
        typ {:t-op ::fn/t-fn
             :t-param {:t-op ::t-hmap
                       :t-fields {(:val expr) (t-exists exists-ret)}}
             :t-ret {:t-op ::bi/t-exists
                     :t-var-name exists-ret}
             :t-field (:val expr)}]
    {:type typ
     :ctx (ctx-conj ctx (c-exists exists-ret))}))

(defmethod typesynth :keyword-invoke
  [ctx expr]
  (when-not (= 1 (count (:args expr))) (throw (ex-info "Keyword invocation is meant to have exactly one argument (no default return value)" {:ctx ctx :expr expr})))
  (let [exists-ret (gensym (:val expr))
        rest (gensym "hmap-rest")
        argtype {:t-op ::t-hmap
                 :t-fields {(:val (:fn expr)) (t-exists exists-ret)}
                 :t-rest {:t-op ::t-hmap-exists
                          :t-var-name rest}}
        ctx' (typecheck (ctx-concat ctx [(c-exists exists-ret)
                                         {:c-op ::c-hmap-exists
                                          :c-fields {}
                                          :c-principal? false
                                          :c-var-name rest}])
                        (first (:args expr)) argtype)
        rettype (type-apply ctx' (t-exists exists-ret))]
    {:type rettype
     :ctx ctx'}))

;; TODO we probably want a statically safe assoc for hmaps and a dynamic assoc for normal maps?
;; This disallows type-changing assocs.
(defmethod typesynth-invoke 'clojure.core/assoc
  [ctx expr]
  (assert (= 3 (count (:args expr))) "annotation should have two arguments: (ann expr type)")
  (let [{ctx :ctx proj :type} (typesynth ctx (second (:args expr)))
        _ (when-not (:t-field proj) (throw (ex-info "Can only assoc hmaps with literal keyword as 2nd arg."
                                                    {:expr expr :type proj})))
        field-v (gensym "assoc-field")
        rest (gensym "hmap-rest")
        ctx (typecheck (ctx-concat ctx [(c-exists field-v)
                                        {:c-op ::c-hmap-exists
                                         :c-fields {}
                                         :c-principal? false
                                         :c-var-name rest}])
                       (first (:args expr))
                       {:t-op ::t-hmap
                        :t-fields {(:t-field proj) (t-exists field-v)}
                        :t-rest {:t-op ::t-hmap-exists
                                 :t-var-name rest}})
        ctx (typecheck ctx
                       (nth (:args expr) 2)
                       (t-exists field-v))]
    {:ctx ctx
     :type (hmap-apply ctx
                       {:t-op ::t-hmap
                        :t-fields {(:t-field proj) (t-exists field-v)}
                        :t-rest {:t-op ::t-hmap-exists
                                 :t-var-name rest}})}))

(defmethod instantiate-poly ::t-hmap
  [ctx t-var-name dir typ]
  (throw (ex-info "TODO instantiate-poly for hmap" {:ctx ctx :typ typ})))

;; A <: B if A has all fields of B, and all A's fields are subtypes of B's matching fields.
;; Existential "rest" variables are instantiated as accurately as possible (which means we don't get silent upcasting)
;; we let the silent upcasts through if the supertype is closed to extra fields.
(defmethod subtype [::t-hmap ::t-hmap]
  [ctx typ1 typ2]
  (let [allkeys (set (concat (keys (:t-fields typ1))  (keys (:t-fields typ2))))
        left-existential  (let [r (:t-rest typ1)] (when (hmap-exists? r) r))
        right-existential (let [r (:t-rest typ2)] (when (hmap-exists? r) r))
        ctx (reduce (fn [ctx key]
                      (let [left-t  (get (:t-fields typ1) key)
                            right-t (get (:t-fields typ2) key)]
                        (cond
                          ;; normal case
                          (and left-t right-t)
                          ,(subtype ctx left-t right-t)
                          ;; We need to refine the right with an extra field
                          (and left-t right-existential)
                          ,(refine-existential ctx right-existential key left-t)
                          ;; We need to refine the left with an extra field
                          (and left-existential right-t)
                          ,(refine-existential ctx left-existential key right-t)
                          ;; We let this implicit upcast through.
                          (and left-t (nil? right-t) (nil? right-existential))
                          ,ctx
                          :else (throw (ex-info "Type error. hmap t1 is not a subtype of hmap t2" {:ctx ctx :key key :typ1 typ1 :typ2 typ2}))
                          )))
                    ctx
                    allkeys)
        ;; and check -rests
        ctx (cond
              (and (nil? left-existential) (nil? right-existential))
              ,ctx
              (and left-existential (nil? right-existential))
              ,(nil-existential ctx left-existential)
              (and (nil? left-existential) right-existential)
              ,(nil-existential ctx right-existential)
              (and left-existential right-existential
                   (= (:t-var-name left-existential)
                      (:t-var-name right-existential)))
              ,ctx
              (and left-existential right-existential
                   (not= (:t-var-name left-existential)
                         (:t-var-name right-existential)))
              ,(unify-existential ctx left-existential right-existential)
              :else (throw (ex-info "Type error. hmap t1 is not a subtype of hmap t2" {:ctx ctx :key ::t-rest :typ1 typ1 :typ2 typ2}))
              )]
    ctx))
