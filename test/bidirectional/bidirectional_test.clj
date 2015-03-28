(ns bidirectional.bidirectional-test
  (:require [clojure.test :refer :all]
            [clojure.tools.analyzer.jvm :as taj]
            [bidirectional.bidirectional :refer :all]))

(deftest checks
  (is (= (renumber-varnames (:type (typesynth [] (taj/analyze+eval '(fn [x] x) (taj/empty-env)))))
         '{:t-op :t-forall, :t-var-name freshes,
           :t-ret {:t-op :t-fn,
                   :t-param {:t-op :t-var, :t-var-name freshes},
                   :t-ret {:t-op :t-var, :t-var-name freshes}}}))
  (is (= (renumber-varnames (:type (typesynth [] (taj/analyze+eval 'nil (taj/empty-env)))))
         {:t-op :t-unit}))
  ;; FIXME - returning a weird (forall a,b. a -> UnknownExistential)
  (is (= (renumber-varnames (:type (typesynth [] (taj/analyze+eval '(fn [x] nil) (taj/empty-env)))))
         {:t-op :t-forall, :t-var-name 'freshes,
          :t-ret {:t-op :t-fn,
                  :t-param {:t-op :t-var, :t-var-name 'freshes},
                  :t-ret {:t-op :t-unit}}}))
  ;; FIXME - it's an existential type not a fn type. I screwed something up. It might also not be possible because it's too polymorphic? But how to get a nicer error message for that?
  #_(is (renumber-varnames (:type (typesynth [] (taj/analyze+eval '((fn [x] x) (fn [x] x)) (taj/empty-env)))))))
