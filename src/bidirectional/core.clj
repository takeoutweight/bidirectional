(ns bidirectional.core
  (:require [clojure.tools.analyzer :as ta]
            [clojure.tools.analyzer.passes.elide-meta :as taem]
            [clojure.tools.analyzer.jvm :as taj]
            [clojure.jvm.tools.analyzer.emit-form :as tae]))

(defn ctx-conj
  [ctx ctx-elem]
  (conj ctx ctx-elem))

(defn ctx-drop
  [ctx ctx-elem]
  (throw (Exception. "TODO")))

(defn e-var
  "a var in expression form.")

(def sample-env
  (assoc (taj/empty-env)
         :locals {'fun1 (taem/elide-meta (taj/analyze+eval '(fn [x] x) (taj/empty-env)))}))

(defn substitute
  "substitution: [new-exp / for-var]expr"
  [new-exp for-var expr]
  (case (:op expr)
    :with-meta (update-in expr :expr #(substitute new-exp for-var %))
    :do (-> expr
            (update-in :statements #(vec (map (fn [s] (substitute new-exp for-var s)) %)))
            (update-in :ret #(substitute new-exp for-var %)))))

(defn typecheck [ctx expr typ]
  (case (:op expr)
    :with-meta (typecheck ctx (:expr expr) typ)
    :fn (do (assert (= :t-fn (:t-op typ)) "type isn't fn type")
            (assert (= 1 (count (:methods expr))) "only single-arity methods supported")
            (assert (= 1 (count (:params (first (:methods expr))))) "only single argument supported")
            (let [ctx-var (gensym (:name (first (:params (first (:methods expr))))))
                  ctx-elem {:c-op :c-var
                            :c-var ctx-var
                            :c-typ (:t-param-typ typ)}]
              (-> (typecheck (ctx-conj ctx ctx-elem) (substitute (e-var ctx-var) ()))
                  (ctx-drop ctx-elem))))))

(defn typesynth [ctx expr]
  (case (:op expr)
    :with-meta (typesynth ctx (:expr expr))
    :fn :TODO))
