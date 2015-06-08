(ns bidirectional.unit-type
  (:require [bidirectional.bidirectional :refer :all :as bi]))

(derive ::t-unit ::bi/t-any-type)

(defmethod type-wf ::t-unit [ctx typ]
  true)

(defmethod map-type ::t-unit [f t] t)

(defmethod monotype? ::t-unit [_] true)

(defmethod free-t-vars ::t-unit [_] #{})

(defmethod typesynth :const [ctx expr]
  (if (= (:val expr) nil)
    {:type {:t-op ::t-unit} :ctx ctx}
    (throw (ex-info "Can't synth type for " expr))))

(defmethod subtype [::t-unit ::t-unit]
  [ctx typ1 typ2]
  ctx)

(defmethod typecheck-m [:const ::t-unit]
  [ctx expr typ]
  ctx)
