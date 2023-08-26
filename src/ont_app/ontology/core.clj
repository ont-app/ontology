(ns ont-app.ontology.core
  (:require
   [clojure.java.io :as io]
   [clojure.spec.alpha :as spec]
   [com.yetanalytics.flint :as flint]
   [ont-app.graph-log.core :as glog]
   [ont-app.graph-log.levels :refer :all]
   [ont-app.igraph.core :as igraph :refer [add
                                           add!
                                           query
                                           subjects
                                           unique
                                           ]]
   [ont-app.igraph.graph :as native-normal]
   [ont-app.igraph-jena.core :as jena]
   [ont-app.rdf.core :as rdf]
   [ont-app.vocabulary.core :as voc :refer [resource-type]]
   )
  (:import
   [org.apache.jena.reasoner
    ReasonerRegistry
    ValidityReport
    ]
   [org.apache.jena.rdf.model
    ModelFactory
    SimpleSelector
    ]
   [org.apache.jena.graph
    NodeFactory
    ]
   [org.apache.jena.fuseki.main
    FusekiServer
    ]
   [org.apache.jena.query
    DatasetFactory
    ]
   [org.apache.jena.riot
    RDFDataMgr
    ]
   #_[openllet.jena
    PelletReasonerFactory
    ]
   [org.topbraid.jenax.util
    JenaUtil
    ]
   ;; This uses old version of Jena...
   #_[org.topbraid.shacl.validation 
    ValidationUtil
    ] 
   [org.topbraid.shacl.rules
    RuleUtil
    ]
   [org.apache.jena.shacl
    ShaclValidator
    Shapes
    ]
   [org.apache.jena.query
    ;; Dataset
    DatasetFactory
    ;;QueryExecution
    ;;QueryExecutionFactory
    ;;QueryFactory
    ]
   )
  (:gen-class))

(voc/put-ns-meta! 'nlx-ont
                  {:vann/preferredNamespaceUri "http://rdf.naturallexicon.org/ontology#"
                   :vann/preferredNamespacePrefix "nlx-ont"
                   })

(voc/put-ns-meta! 'natlex
                  {:vann/preferredNamespaceUri "http://rdf.naturallexicon.org/terms#"
                   :vann/preferredNamespacePrefix "natlex"
                   })
(voc/put-ns-meta! 'validation
                  {:vann/preferredNamespaceUri "http://rdf.naturallexicon.org/validation#"
                   :vann/preferredNamespacePrefix "validation"
                   })

(def fbr (ReasonerRegistry/getOWLReasoner))
(def rdfs-reasoner (ReasonerRegistry/getRDFSReasoner))
(def micro (ReasonerRegistry/getOWLMicroReasoner))


#_(defmethod voc/as-uri-string :voc/QualifiedNonKwi
  [kw]
  (if (rdf/bnode-kwi? kw)
    (str "_:" (name kw))
    (throw (ex-info (str "Cannot create URI for " kw)
                    {:type :cannot-create-uri-for-kw
                     ::kw kw
                     }))))

(defn drop-graph!
  "Side-effect: removes graph named by `graph-name` from `dataset`
  - Where
    - `dataset` is a jena dataset
    - `graph-name` is a voc/resource-type
  "
  [dataset graph-name]
  (.removeNamedModel dataset
                     (voc/as-uri-string graph-name)))

(defn install-inference-model
  [dataset reasoner graph-name-resource]
  (let [base-model (.getDefaultModel dataset)
        inference-model (ModelFactory/createInfModel reasoner base-model)
        ]
    (.addNamedModel dataset (voc/as-uri-string graph-name-resource) inference-model)
    (jena/make-jena-graph dataset graph-name-resource)))

(def catalog-cache (atom (native-normal/make-graph)))
(defn clear-catalog-cache!
  []
  (reset! catalog-cache (native-normal/make-graph)))

(defn build-catalog
  "Returns: `catalog`
  - Where
    - `catalog` is a jena igraph containing a description of RDF resources
    - `dataset` is a jena dataset containing `catalog`
    
  "
  [dataset catalog-kwi]
  (let [catalog (jena/make-jena-graph dataset catalog-kwi)
        ]
    (add! catalog
          [[:test/RectangleRules
           :rdf/type :natlex/Graph
           :dcat/downloadURL (java.net.URL. "https://raw.githubusercontent.com/TopQuadrant/shacl/master/src/test/resources/sh/tests/rules/sparql/rectangle.test.ttl")
            ]
           [:nlx-ont/Top
            :rdf/type :natlex/Graph
            :dcat/downloadURL (io/resource "natural-lexicon.ttl")
            ]
           [:nlx-ont/Characterization
            :rdf/type :natlex/Graph
            :dcat/downloadURL (io/resource "characterization.ttl")
            ]           
           [:nlx-ont/Temporality
            :rdf/type :natlex/Graph
            :dcat/downloadURL (io/resource "temporality.ttl")
            :natlex/validator :validation/Temporality
            ]
           [:nlx-ont/Modality
            :rdf/type :natlex/Graph
            :dcat/downloadURL (io/resource "modality.ttl")
            ]
           [:nlx-ont/Significance
            :rdf/type :natlex/Graph
            :dcat/downloadURL (io/resource "significance.ttl")
            ]
           ]
    )))

(defn reset-catalog!
  "Call this to reload the RDF resources.
  - Where
    - `io-context` is the output of `create-dataset-io-context`
    - `catalog-kwi` names the catalog graph for the dataset in `io-context`
  "
  [io-context catalog-kwi]
  (if-let [ds (unique (io-context :jena/Dataset :igraph/compiledAs))]
    (let []
      (rdf/clear-url-cache! io-context)  
      (clear-catalog-cache!)
      (drop-graph! ds catalog-kwi)
      (build-catalog ds catalog-kwi))
    (throw (ex-info "I/O context does not include dataset spec"
                    {:type ::io-context-error
                     ::io-context io-context}))))
                    
(defn load-from-catalog
  "Side-effects: Reads content associated with `kwi` in `catalog` into `g` and caches `g` in @`catalog-cache`
  Returns: `g`
  - Where:
    - `io-context` is the output of `create-dataset-io-context` 
    - `catalog` is an jena igraph containing descriptions of RDF content
    - `g` is a jena igraph containing the contents of `kwi`
    - `kwi` is a resource named in `catalog` containing RDF contents for `g`
  "
  ([io-context catalog kwi]
   (if-let [cached (unique (@catalog-cache kwi :igraph/compiledAs))]
     (value-trace
      ::load-from-catalog-cache-hit
      [::kwi kwi]
      cached)
     ;; else not cached
     (value-trace
      ::load-from-catalog-cache-miss
      [::kwi kwi]
      (let [dataset (unique (io-context :jena/Dataset :igraph/compiledAs))
            g (jena/make-jena-graph dataset kwi)
            ]
        (swap! catalog-cache add [[kwi :igraph/compiledAs g]
                                  [g :natlex/cachedValueOf kwi]])
        (load-from-catalog io-context catalog g kwi)
        ))))
  ([_io-context catalog g kwi]
   (value-trace
    ::load-from-catalog-read-from-download-url
    [::g g ::kwi kwi]
    (jena/read-rdf g (-> (unique (catalog kwi :dcat/downloadURL))
                         voc/as-uri-string
                         (java.net.URL.)
                         )))
   g))

(defn create-dataset-io-context
  "Returns an I/O context for `dataset`
  - Where
    - `dataset` is a jena dataset.
    - i/o context is the context argument for rdf i/o methods
  "
  [dataset]
  (add jena/standard-io-context
       [:jena/Dataset :igraph/compiledAs dataset]))


(defn add-from-catalog!
  [io-context catalog g graph-name]
  (load-from-catalog io-context catalog g graph-name))

;;;;;;;;;;;;;;;;;
;; FLINT SUPPORT
;;;;;;;;;;;;;;;;;

(defn collect-prefixes
  "Returns {`prefix` `uri`, ...} for any KWIs in `m` suitable as prefix map for a flint query map.
  - Where
    - `m` is a nested sequence, typically a map
    - `prefix` is a keyword naming a prefix
    - `uri` is a <angle-bracketed-uri>
  "
  [m]
  (let [prefixes (atom {})
        collect-prefix (fn [elt]
                         (when (spec/valid? :voc/kwi-spec elt)
                           (let [ns' (namespace elt)]
                             (when-let [uri (->
                                             (voc/prefixed-ns ns')
                                             (voc/ns-to-namespace))]
                               (swap! prefixes
                                      assoc
                                      (keyword ns')
                                      (str "<" (voc/as-uri-string uri) ">"))))))
        ]
    (clojure.walk/postwalk collect-prefix m)
    @prefixes))

(defn flint-query
  "Returns a query for `query-map`
  - Where
    - `query-map` := m s.t. (keys m :~ #{:select :where}, conforming to keys expected in flint. The :prefixes field will be automatically populated.
  - NOTE: currently only the vector-of-vectors syntax is supported
  - SEE ALSO: https://github.com/yetanalytics/flint
  "
  [query-map]
  (let []
    (-> (merge query-map
               {:prefixes (collect-prefixes query-map)})
        (flint/format-query))))

(defn lstr-to-flint-map
  "Returns {`lang` `str} from `lstr` (for flint queries)
  - Where
    - `lstr` is a language tagged literal #voc/lstr ...
    - `lang` is a language tag
    - `str` is the content
  "
  [lstr]
  {(keyword (ont-app.vocabulary.lstr/lang lstr)) (str lstr)})

;;;;;;;;;;;;;;
;; UTILITIES
;;;;;;;;;;;;;;

(defn now []
  "Returns the current time as an #inst"
  (java.util.Date.))

(defn g-grep
  "Applies `regex` to every element in `g`, returning the set of matches."
  [g regex]
  (let [collect-element (fn [sacc elt]
                          (if (re-matches regex (str elt))
                            (conj sacc elt)
                            sacc))
        collect-spo (fn [sacc s p o]
                      (collect-element sacc s)
                      (collect-element sacc p)
                      (collect-element sacc o))
        ]
    (igraph/reduce-spo collect-spo #{} g)))

(defn g-apropos
  "Returns the set of all elements in `g` containing `substring`. Case insensitive"
  [g substring]
  (let [collect-element (fn [sacc elt]
                          (if (re-find (re-pattern (str "(?i)" substring))
                                       (str elt))
                            (conj sacc elt)
                            sacc))
        collect-spo (fn [sacc s p o]
                      (collect-element sacc s)
                      (collect-element sacc p)
                      (collect-element sacc o))
        ]
    (igraph/reduce-spo collect-spo #{} g)))

(defn triples-with-element
  "Returns #{[s p o],...} for triples in `g` containing `elt`
  - Where
    - `elt` is one of `s` `p` or `o`
  "
  [g elt]
  (let [do-collect-element (fn [triple sacc elt']
                             (if (= elt elt')
                               (conj sacc triple)
                               sacc))
        collect-spo (fn [sacc s p o]
                      (let [collect-element (partial do-collect-element [s p o])]
                        (collect-element sacc s)
                        (collect-element sacc p)
                        (collect-element sacc o)))
        ]
    (igraph/reduce-spo collect-spo #{} g)))

(defn describe-domain
  [g class']
  (query g (flint-query `{:select [?property ?description]
                          :where [{?property
                                   {:rdfs/domain #{~class'}
                                    :dc/description #{?description}}}
                                  ]
                          :order-by [?property]
                          })))

(defn describe-range
  [g class']
  (query g (flint-query `{:select [?property ?description]
                          :where [{?property
                                   {:rdfs/range #{~class'}
                                    :dc/description #{?description}}}
                                  ]
                          :order-by [?property]
                          })))

(defn find-orphans
  "Returns #{`orphan`, ...} in `g`
  - where
    - `g` is an ontology
    - `orphan` is a class in `g` which has no documentation strings, and thus not properly declared.
  "
  [g]
  (->> (query g (flint-query '{:select [?orphan]
                               :where [[?orphan :rdf/type ?class]
                                       [:values {?class [:rdfs/Class :rdf/Property]}]
                                       [:filter (not-exists
                                                 [[?orphan
                                                   (alt :rdfs/comment :dc/description)
                                                   ?desc]])]
                                       ]}))
       (map :orphan)
       (filter (fn [kwi] (not (#{"xsd" "rdf" "owl" "rdfs" "sh" "jena" "vcard" "skos" "dc"}
                               (namespace kwi)))))))



;;;;;;;;;;;;;;;
;; DERIVATIONS
;; see https://jena.apache.org/documentation/inference/#derivations
;;;;;;;;;;;;;;;

(defn explain-statement
  "Side-effect: creates `file` with inference derivations of `statement` in `g`"
  [g statement file]
  (with-open [out-stream (java.io.PrintWriter. (io/writer file))
              ]
    (let [ds (.getDerivation (:model g) statement)
          ]
      (while (.hasNext ds)
        (.printTrace (.next ds) out-stream true))))
  file)

(defn list-derivations
  "Side-effect: writes all derivations for `g` to `file`
  - Where
    - `g` is a graph acquired while (.setDerivationLogging <inferencer> true)
    - `file` is a string naming the output file.
  "
  [g file]
  (let [ss (.listStatements (:model g))
        get-derivation (fn [statement] (.getDerivation (:model g) statement))
        ]
    (with-open [out-stream (java.io.PrintWriter. (io/writer file))
                ]
      (while (.hasNext ss)
        (let [s (.nextStatement ss)
              ds (get-derivation s)
              ]
          (while (.hasNext ds)
            (.printTrace (.next ds) out-stream true)))))))

(defn get-next-statement
  "Returns next statement from `statements`, or nil
  - Where
    - `statements` is a Java iterator, typically returned by (.listStatements ...)
  "
  [^org.apache.jena.rdf.model.impl.StmtIteratorImpl statements]
  (if (.hasNext statements)
    (.next statements)))

(defn get-all-statements
  "Returns (`statement`, ...) for all `s` `p `o` in `g`
  - Where
    - `g` is a graph acquired while (.setDerivationLogging <inferencer> true)
    - `statement` is a StatementImpl"
  [g s p o]
  (let [create-resource (fn [x] (.createResource (:model g) (voc/as-uri-string x)))
        maybe-create-resource (fn [x]
                                (case (voc/resource-type x)
                                  :voc/Kwi
                                  (create-resource x)

                                  :voc/QualifiedNonKwi
                                  (if (rdf/bnode-kwi? x)
                                    nil
                                    (throw (ex-info
                                            "Non-qualified kwi"
                                            {:type ::non-qualified-kwi
                                             ::x x
                                             })))
                                  ;; default
                                  nil
                                  ))

        statement-iterator (.listStatements (:model g)
                                            (maybe-create-resource s)
                                            (.createProperty (:model g)
                                                             (voc/as-uri-string p))
                                            (maybe-create-resource o))
        match-bnode-object (fn [statement]
                             (if (rdf/bnode-kwi? o)
                               (let [obj (.getObject statement)]
                                 (= (str "_:" obj)
                                    (clojure.string/replace (name o) #"[<>]" "")))
                               ;; else not a bnode
                               true))
        ]
    (filter match-bnode-object
            (take-while identity (repeatedly #(get-next-statement statement-iterator))))))

(defn -main
  "I don't do a whole lot ... yet."
  [& args]
  (println "Hello, World!"))
