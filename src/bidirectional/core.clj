(ns bidirectional.core
  (:require [clojure.tools.analyzer :as ta]
            [clojure.tools.analyzer.passes.elide-meta :as taem]
            [clojure.tools.analyzer.jvm :as taj]
            [clojure.jvm.tools.analyzer.emit-form :as tae]))

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

(defn ctx-drop
  [ctx ctx-elem]
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

(defn typecheck [ctx expr typ]
  (case (:op expr)
    :with-meta (typecheck ctx (:expr expr) typ)
    :fn (do (assert (= :t-fn (:t-op typ)) "type isn't fn type")
            (assert (= 1 (count (:methods expr))) "only single-arity methods supported")
            (assert (= 1 (count (:params (first (:methods expr))))) "only single argument supported")
            (let [param-name (:name (first (:params (first (:methods expr)))))
                  ctx-var-name (gensym param-name) ; Since param-name is gensymmed, I'm guessing we can just use the existing one and avoid the renaming?
                  ctx-elem {:c-op :c-var
                            :c-var ctx-var-name
                            :c-typ (:t-param-typ typ)}]
              (-> (typecheck (ctx-conj ctx ctx-elem) (rename-var ctx-var-name param-name) (:t-ret-typ typ))
                  (ctx-drop ctx-elem))))))

(defn typesynth [ctx expr]
  (case (:op expr)
    :with-meta (typesynth ctx (:expr expr))
    :fn :TODO))
