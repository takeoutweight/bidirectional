(ns bidirectional.bidirectional-test
  (:require [clojure.test :refer :all]
            [clojure.tools.analyzer.jvm :as taj]
            [bidirectional.bidirectional :refer :all :as bi]
            [bidirectional.fn-type :as ft]
            [bidirectional.hmap-type :as ht]
            [bidirectional.unit-type :as ut])
  (:import clojure.lang.ExceptionInfo))

(deftest checks
  (is (= (infer '(fn [x] x))
         '{:t-op ::bi/t-forall, :t-var-name freshes,
           :t-ret {:t-op ::ft/t-fn,
                   :t-param {:t-op ::bi/t-var, :t-var-name freshes},
                   :t-ret {:t-op ::bi/t-var, :t-var-name freshes}}}))
  (is (= (infer 'nil)
         {:t-op ::ut/t-unit}))
  (is (= (infer '(fn [x] nil))
         {:t-op ::bi/t-forall, :t-var-name 'freshes,
          :t-ret {:t-op ::ft/t-fn,
                  :t-param {:t-op ::bi/t-var, :t-var-name 'freshes},
                  :t-ret {:t-op ::ut/t-unit}}}))
  (is (= (infer '((fn [x] (x nil)) (fn [x] x)))
         {:t-op ::ut/t-unit})
      "higher order fns work")
  (is (= (check '(fn [x] nil)
                {:t-op ::bi/t-forall :t-var-name 'a
                 :t-ret {:t-op ::ft/t-fn
                         :t-param {:t-op ::bi/t-var :t-var-name 'a}
                         :t-ret {:t-op ::ut/t-unit}}})
         [])
      "Checking agrees with inference")
  (is (= (infer '(bidirectional.bidirectional/ann
                  (fn [x] nil) {:t-op ::ft/t-fn
                                :t-param {:t-op ::ut/t-unit}
                                :t-ret   {:t-op ::ut/t-unit}}))
         {:t-ret {:t-op ::ut/t-unit}, :t-param {:t-op ::ut/t-unit}, :t-op ::ft/t-fn})
      "explicit annotations synthesize the annotated type")
  (is (= (infer '((fn [x] (x nil)) (bidirectional.bidirectional/ann
                                    (fn [x] x) {:t-op ::bi/t-forall, :t-var-name 'a,
                                                :t-ret {:t-op ::ft/t-fn,
                                                        :t-param {:t-op ::bi/t-var, :t-var-name 'a},
                                                        :t-ret {:t-op ::bi/t-var, :t-var-name 'a}}})))
         {:t-op ::ut/t-unit})
      "You can annotate argument sub-expressions")
  (is (thrown? clojure.lang.ExceptionInfo
               (check '(fn [x] nil)
                      {:t-op ::bi/t-forall :t-var-name 'a
                       :t-ret {:t-op ::ft/t-fn
                               :t-param {:t-op ::bi/t-var :t-var-name 'a}
                               :t-ret   {:t-op ::bi/t-var :t-var-name 'a}}}))
      "you can't wrongly promise polymorphic return")
  ;; Q: Following examples, typesynth doesn't type-apply its return value, you have to remember. Is this important or incidental?
  (is (= (renumber-varnames (:type (typesynth [] (taj/analyze+eval '((fn [x] x) nil) (taj/empty-env)))))
         {:t-op ::bi/t-exists, :t-var-name 'invokeforall}))
  (is (= (infer '((fn [x] x) nil))
         {:t-op ::ut/t-unit})
      "function application fixes polymorphic fns")
  (is (= (check '(fn [x] x) {:t-op ::ft/t-fn :t-param {:t-op ::ut/t-unit} :t-ret {:t-op ::ut/t-unit}})
         [])
      "can check a polymorphic fn at a less polymorphic type")
  (is (= (check '(fn [x] nil) {:t-op ::bi/t-forall :t-var-name 'a :t-ret {:t-op ::ft/t-fn :t-param {:t-op ::ut/t-unit} :t-ret {:t-op ::ut/t-unit}}})
         [])
      "un-used polymorphic variables are OK")
  ;; Is this right? due to prenex polymorphism it must resolve to some monotype?
  (is (= (infer '((fn [x] x) (fn [x] x)))
         {:t-op ::ft/t-fn,
          :t-param {:t-op ::bi/t-exists, :t-var-name 'G},
          :t-ret {:t-op ::bi/t-exists, :t-var-name 'G}}))
  ;; and is THIS right as well?
  (is (= (infer '(bidirectional.bidirectional/ann
                  ((fn [x] x) (fn [x] x)) {:t-op ::bi/t-forall :t-var-name 'a
                                           :t-ret {:t-op ::ft/t-fn
                                                   :t-param {:t-op ::bi/t-var :t-var-name 'a}
                                                   :t-ret   {:t-op ::bi/t-var :t-var-name 'a}}}))
         {:t-op ::bi/t-forall :t-var-name 'a
          :t-ret {:t-op ::ft/t-fn
                  :t-param {:t-op ::bi/t-var :t-var-name 'a}
                  :t-ret   {:t-op ::bi/t-var :t-var-name 'a}}})
      "If we explicitly ask for polymorphism on the fancy application we get it")
  (is (= (infer '(bidirectional.bidirectional/ann
                  ((fn [x] x) (fn [x] x)) {:t-op ::bi/t-forall :t-var-name 'a
                                           :t-ret {:t-op ::ft/t-fn
                                                   :t-param {:t-op ::ut/t-unit}
                                                   :t-ret   {:t-op ::ut/t-unit}}}))
         {:t-op ::bi/t-forall :t-var-name 'a
          :t-ret {:t-op ::ft/t-fn
                  :t-param {:t-op ::ut/t-unit}
                  :t-ret   {:t-op ::ut/t-unit}}})
      "fancy application can be fixed to a monotype with an annotation"))

(deftest hmap-test
  (is (= (infer '{:x nil})
         {:t-op ::ht/t-hmap, :t-fields {:x {:t-op ::ut/t-unit}}, :t-rest {:t-op ::ht/t-hmap-nil}})
      "infer basic hmaps")
  (is (= (infer '(:x {:x {:y nil}}))
         {:t-op ::ht/t-hmap, :t-fields {:y {:t-op ::ut/t-unit}}, :t-rest {:t-op ::ht/t-hmap-nil}})
      "infer projections")
  (is (thrown-with-msg? ExceptionInfo #"is not a subtype"
                        (infer '(assoc {:x nil} :x (fn [x] x))))
      "can't use assoc to change type")
  (is (= (infer '(assoc {:x nil} :x nil))
         {:t-op ::ht/t-hmap, :t-fields {:x {:t-op ::ut/t-unit}}, :t-rest {:t-op ::ht/t-hmap-nil}})
      "don't forget principality")
  ;;; TODO Waiting on instantiate-poly
  #_(infer '(((fn [x] (fn [y] (x y))) :x) {:x nil})))
