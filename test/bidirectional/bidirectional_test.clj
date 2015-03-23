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
  ;; FIXME - it's an existential type not a fn type. I screwed something up.
  (is (renumber-varnames (:type (typesynth [] (taj/analyze+eval '((fn [x] x) (fn [x] x)) (taj/empty-env)))))))
