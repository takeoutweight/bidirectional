(defproject bidirectional "0.1.0-SNAPSHOT"
  :description "FIXME: write description"
  :url "http://example.com/FIXME"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :dependencies [[org.clojure/clojure "1.6.0"]
                 [org.clojure/core.match "0.3.0-alpha4"]
                 [org.clojure/tools.analyzer.jvm "0.3.0"] ;; for most of the analysis
                 [org.clojure/jvm.tools.analyzer "0.6.1" ;; just for emit-form
                  :exclusions [org.clojure/clojure
                               org.clojure/clojurescript]]])
