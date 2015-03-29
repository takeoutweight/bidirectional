(ns bidirectional.bidirectional-test
  (:require [clojure.test :refer :all]
            [clojure.tools.analyzer.jvm :as taj]
            [bidirectional.bidirectional :refer :all]))

(deftest checks
  (is (= (infer '(fn [x] x))
         '{:t-op :t-forall, :t-var-name freshes,
           :t-ret {:t-op :t-fn,
                   :t-param {:t-op :t-var, :t-var-name freshes},
                   :t-ret {:t-op :t-var, :t-var-name freshes}}}))
  (is (= (infer 'nil)
         {:t-op :t-unit}))
  (is (= (infer '(fn [x] nil))
         {:t-op :t-forall, :t-var-name 'freshes,
          :t-ret {:t-op :t-fn,
                  :t-param {:t-op :t-var, :t-var-name 'freshes},
                  :t-ret {:t-op :t-unit}}}))
  (is (= (infer '((fn [x] (x nil)) (fn [x] x)))
         {:t-op :t-unit})
      "higher order fns work")
  (is (= (check '(fn [x] nil)
                {:t-op :t-forall :t-var-name 'a
                 :t-ret {:t-op :t-fn
                         :t-param {:t-op :t-var :t-var-name 'a}
                         :t-ret {:t-op :t-unit}}})
         [])
      "Checking agrees with inference")
  (is (= (infer '(ann (fn [x] nil) {:t-op :t-fn
                                    :t-param {:t-op :t-unit}
                                    :t-ret   {:t-op :t-unit}}))
         {:t-ret {:t-op :t-unit}, :t-param {:t-op :t-unit}, :t-op :t-fn})
      "explicit annotations synthesize the annotated type")
  (is (= (infer '((fn [x] (x nil)) (ann (fn [x] x) {:t-op :t-forall, :t-var-name 'a,
                                                    :t-ret {:t-op :t-fn,
                                                            :t-param {:t-op :t-var, :t-var-name 'a},
                                                            :t-ret {:t-op :t-var, :t-var-name 'a}}})))
         {:t-op :t-unit})
      "You can annotate argument sub-expressions")
  (is (thrown? clojure.lang.ExceptionInfo
               (check '(fn [x] nil)
                      {:t-op :t-forall :t-var-name 'a
                       :t-ret {:t-op :t-fn
                               :t-param {:t-op :t-var :t-var-name 'a}
                               :t-ret   {:t-op :t-var :t-var-name 'a}}}))
      "you can't wrongly promise polymorphic return")
  ;; Q: Following examples, typesynth doesn't type-apply its return value, you have to remember. Is this important or incidental?
  (is (= (renumber-varnames (:type (typesynth [] (taj/analyze+eval '((fn [x] x) nil) (taj/empty-env)))))
         {:t-op :t-exists, :t-var-name 'invokeforall}))
  (is (= (infer '((fn [x] x) nil))
         {:t-op :t-unit})
      "function application fixes polymorphic fns")
  (is (= (check '(fn [x] x) {:t-op :t-fn :t-param {:t-op :t-unit} :t-ret {:t-op :t-unit}})
         [])
      "can check a polymorphic fn at a less polymorphic type")
  (is (= (check '(fn [x] nil) {:t-op :t-forall :t-var-name 'a :t-ret {:t-op :t-fn :t-param {:t-op :t-unit} :t-ret {:t-op :t-unit}}})
         [])
      "un-used polymorphic variables are OK")
  ;; Is this right? due to prenex polymorphism it must resolve to some monotype?
  (is (= (infer '((fn [x] x) (fn [x] x)))
         {:t-op :t-fn,
          :t-param {:t-op :t-exists, :t-var-name 'G},
          :t-ret {:t-op :t-exists, :t-var-name 'G}})))
