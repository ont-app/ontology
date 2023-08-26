(ns ont-app.ontology.core-test
  {:vann/preferredNamespaceUri "urn:test:data:"
   :vann/preferredNamespacePrefix "test"
   }
  (:require [clojure.test :refer :all]
            [cljstache.core :as stache]
            [clojure.repl :refer :all]
            [clojure.reflect :refer [reflect]]
            [clojure.java.io :as io]
            [clojure.spec.alpha :as spec]
            [com.yetanalytics.flint :as flint]
            [ont-app.ontology.core :as ontology :refer [
                                                        build-catalog
                                                        catalog-cache
                                                        clear-catalog-cache!
                                                        create-dataset-io-context
                                                        describe-domain
                                                        describe-range
                                                        explain-statement
                                                        fbr
                                                        find-orphans
                                                        flint-query
                                                        g-apropos
                                                        get-next-statement
                                                        get-all-statements
                                                        g-grep
                                                        install-inference-model
                                                        list-derivations
                                                        micro
                                                        now
                                                        rdfs-reasoner
                                                        triples-with-element
                                                        ]]
            [ont-app.vocabulary.core :as voc :refer []]
            [ont-app.vocabulary.wikidata :as wd :refer []]
            [ont-app.rdf.core :as rdf]
            [ont-app.igraph-jena.core :as jena]
            [ont-app.igraph.graph :as native-normal]
            [ont-app.igraph-vocabulary.core :as igv :refer [mint-kwi]]
            [ont-app.igraph.core :as igraph :refer [add
                                                    add!
                                                    normal-form
                                                    query
                                                    subjects
                                                    subtract!
                                                    t-comp
                                                    unique
                                                    ]]

            [ont-app.sparql-client.core :as sparql-client]
            [ont-app.graph-log.core :as glog]
            [ont-app.vocabulary.core :as voc]
            [ont-app.vocabulary.wikidata :as wd]
            )
  (:import   [org.apache.jena.reasoner
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
    QueryExecutionFactory
    QueryFactory
    ]
   ))

(defn log-reset!
  "Side-effect: enables graph-log with `level` (default `:glog/DEBUG`)"
  ([]
   (log-reset! :glog/TRACE))
  ([level]
   (glog/log-reset!)
   (glog/set-level! level)))

(def prefixed voc/prepend-prefix-declarations)

;;;;;;;;;;;;;;;
;; ONT-API
;;;;;;;;;;;;;;;
#_(def omi (OntManagers/createManager))

;; (.loadOntology omi (IRI/create (voc/as-uri-string test-content))))


;;;;;;;;;;;;;
;; Content
;;;;;;;;;;;;


(def dataset (DatasetFactory/create))

(def dataset-io-context (create-dataset-io-context dataset))


(def test-catalog (build-catalog dataset :test/Catalog))

(defn reset-catalog! [] (ontology/reset-catalog! dataset-io-context :test/Catalog))

(def load-from-catalog (partial ontology/load-from-catalog
                                dataset-io-context
                                test-catalog))

(def add-from-catalog! (partial ontology/add-from-catalog!
                                dataset-io-context
                                test-catalog))

;;(def fundamentals (clojure.java.io/file "/home/eric/Data/RDF/natural-lexicon.ttl"))
(def test-content (io/resource "natural-lexicon.ttl"))
(def previous-content (io/file "/home/eric/Data/RDF/natural-lexicon.ttl "))


(.setDerivationLogging rdfs-reasoner true) ;; explains inferencing
(.setDerivationLogging micro true) ;; explains inferencing

(comment
(defn reload-library []
  (rdf/clear-url-cache! dataset-io-context)
  (rdf/load-rdf dataset-io-context (io/resource "library.ttl")))
  )


(.setDerivationLogging rdfs-reasoner true) ;; explains inferencing
(.setDerivationLogging micro true) ;; explains inferencing

  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; CHECK PULSE FROM SHACL LIBRARY
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  
(voc/put-ns-meta! 'rectangle-test
                  {:vann/preferredNamespaceUri "http://datashapes.org/shasf/tests/rules/sparql/rectangle.test#"
                   :vann/preferredNamespacePrefix "rectangle-test"
                   })

(defn get-rectangle-rules []
  (load-from-catalog :test/RectangleRules))


(def rectangle-rules (get-rectangle-rules))


(defn test-shacl
  []
  (let [g  (-> (RuleUtil/executeRules (:model rectangle-rules) (:model rectangle-rules) nil nil)
               (jena/make-jena-graph))
        ]
    (g :rectangle-test/#ExampleRectangle)))
             

(defn shapes-graph-for
  [g]
  (as-> g it
    (@catalog-cache it :natlex/cachedValueOf)
    (unique it)
    (test-catalog it :natlex/validator)
    (unique it)
    (load-from-catalog it)
    (add! g (igraph/normal-form it))
    ))

(defn validate-model
  [data shapes]
  (let [validator (ShaclValidator/get)
        shapes (Shapes/parse (:model shapes))
        ]
    (-> (.validate validator shapes (.getInfGraph (:model data)))
        (.getModel)
        (jena/make-jena-graph))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DEFINE SHACL RULES TO INFORM THE UPPER ONTOLOGY
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def disjoint-classes-query "
Select Distinct ?member ?otherMember
Where
{
  ?allDisjoint a owl:AllDisjointClasses;
    owl:members/rdf:rest*/rdf:first ?member;
    owl:members/rdf:rest*/rdf:first ?otherMember;
  .
  Filter (?member != ?otherMember)
}")

(defn render-shacl-disjoint-class-rule
  [query-binding]
  (let [member (:member query-binding)
        other-member (:otherMember query-binding)
        template "
validation:{{{node-uri-name}}
     a sh:NodeShape ;
     sh:targetClass {{member-uri}} ;
     sh:property [
         sh:path rdf:type ;
         sh:not [sh:hasValue {{other-member-uri}}] ;
         sh:severity sh:Violation ;
         sh:message {{{message}}} ;
    ] ;
 ."]
    (stache/render template
                   {:node-uri-name (str "ClassDisjunction_"
                                        (name member)
                                        "_"
                                        (name other-member))
                    :member-uri (voc/as-qname member)
                    :other-member-uri (voc/as-qname other-member)
                    :message (rdf/quote-str
                              (str (voc/as-qname member)
                                   " is disjoint from "
                                   (voc/as-qname  other-member)))
                    })))
       

(defn shacl-rules-to-enforce-disjoint-classes
  "Returns `g-target` containing disjoint-class rules derived from OWL2 declarations of disjoint classes."
  [g-source g-target]
  (let [results-graph (native-normal/make-graph)
        results (igraph/query g-source (prefixed disjoint-classes-query))
        collect-rule (fn [acc b]
                       (str acc (render-shacl-disjoint-class-rule b)))
        ]
    (rdf/read-rdf dataset-io-context
                  g-target 
                  (voc/prepend-prefix-declarations
                   voc/turtle-prefixes-for
                   (reduce collect-rule "" results)))
    g-target))

(comment
  (def g' (shacl-rules-to-enforce-disjoint-classes g (jena/make-jena-graph)))
  (def r (validate-model g g'))
  )

(def has-quanity-construct-query
  "
CONSTRUCT
{
  ?magnitude natlex:hasQuantity ?quantity.
  ?observation natlex:quantifiedAs ?magnitude.
}
WHERE
{
  {
    ?magnitude a natlex:Magnitude;
      natlex:primaryFigureOf/natlex:quantifiedAs ?quantity.
    FILTER NOT EXISTS {?this natlex:hasQuantity ?quantity}
  }
  UNION
  {
    ?magnitude natlex:hasQuantity ?quantity.
    ?observation natlex:ofPrimaryFigure ?magnitude.
    FILTER NOT EXISTS {?observation natlex:quantifiedAs ?quantity}
  }
}
"
  )

(defn get-basic-rules
  []
  (ontology/drop-graph! dataset :natlex/InferenceRules)
  (-> (jena/make-jena-graph dataset :natlex/InferenceRules )
      (add! [
             [:natlex/HasQuantityRuleShape
              :sh/description " magnitude X has quantity Y <-> observation of X quantified as Y"
              :rdf/type :sh/NodeShape
              :sh/rule :natlex/HasQuantityRule
              :sh/targetNode :sh/this
              ]
             [:natlex/HasQuantityRule
              :rdf/type :sh/SPARQLRule
              :sh/construct (rdf/remove-newlines (prefixed has-quanity-construct-query))

              ]
             ])))
  
(def basic-rules  (get-basic-rules))

(defn reload []
  "Returns an IGraph configured with an inferencer and pupulated with a schema"
  (let [im (->> (ModelFactory/createDefaultModel)
                (ModelFactory/createInfModel micro))
        ]
    (-> (jena/make-jena-graph im)
        (add-from-catalog! :nlx-ont/Top)
        #_(jena/read-rdf test-content))))

(deftest is-relative-to-loaded?
;;  (ontology/clear-catalog-cache!)
  (ontology/reset-catalog! dataset-io-context :test/Catalog)
  (let [g (reload)]
    (is (not (empty? (g :natlex/relativeTo))))))


(defn get-content
  "Acquires the basic graph and schema and adds test data."
  []
  (let [g (reload)
        ]
    (add! g [:natlex/TestEntity :natlex/hasPart :natlex/TestPart])
    (add! g [:natlex/TestScan :natlex/byObserver :natlex/TestObserver])
    (add! g [:natlex/TestScan :natlex/ofPrimaryFigure :natlex/TestTrajector])
    (add! g [:natlex/TestScan :natlex/withSecondaryFigure :natlex/TestLandmark])
    (add! g [:natlex/TestScan :natlex/qualifiedAs :natlex/TestQuality])
    (add! g [:natlex/TestScan :natlex/quantifiedAs :natlex/TestQuantity])
    (add! g [:natlex/TestEntity :natlex/relativeBasisOf :natlex/TestSpace])
    (add! g [:natlex/TestQuantityAssessment
             :natlex/ofPrimaryFigure :natlex/TestMagnitude
             ])
    (add! g [:natlex/TestMagnitude :natlex/hasQuantity 42])

    ))

(defn test-basic-rules
  []
  ;; <data model> <shapes model> <inferences model> <progress monitor>
  (let [content (get-content)
        ]
    (let [new-content (-> (RuleUtil/executeRules (:model content)
                                                 (:model (get-basic-rules))
                                                 nil
                                                 nil)
                          jena/make-jena-graph)
          ]
      (add! content (igraph/normal-form new-content))
    )))



(deftest do-test-basic-rules
  (let [g (test-basic-rules)
        ]
    (is (= (g :natlex/TestEntity)
           {:natlex/relativeBasisOf #{:natlex/TestSpace},
            :natlex/hasPart #{:natlex/TestPart},
            :natlex/integrates #{:natlex/TestPart :natlex/TestSpace},
            :rdf/type #{:natlex/Entity :owl/Thing :rdfs/Resource}}
           ))

    (is (= (g :natlex/TestPart)
           {:rdf/type #{:natlex/Entity :owl/Thing :rdfs/Resource},
            :natlex/partOf #{:natlex/TestEntity},
            :natlex/integralTo #{:natlex/TestEntity}
            }
           ))
    
    (is (= (g :natlex/TestScan)
           {:rdf/type
            #{:natlex/Relationship
              :natlex/Observation
              :owl/Thing
              :rdfs/Resource},
            :natlex/quantifiedAs #{:natlex/TestQuantity},
            :natlex/assessedAs #{:natlex/TestQuantity :natlex/TestQuality},
            :natlex/hasParticipant
            #{:natlex/TestQuantity
              :natlex/TestLandmark
              :natlex/TestQuality
              :natlex/TestTrajector
              :natlex/TestObserver},
            :natlex/withSecondaryFigure #{:natlex/TestLandmark},
            :natlex/ofPrimaryFigure #{:natlex/TestTrajector},
            :natlex/integrates
            #{:natlex/TestQuantity
              :natlex/TestLandmark
              :natlex/TestQuality
              :natlex/TestTrajector
              :natlex/TestObserver},
            :natlex/qualifiedAs #{:natlex/TestQuality},
            :natlex/byObserver #{:natlex/TestObserver}}
           ))
    
    (is (= (g :natlex/TestObserver)
           {:natlex/observerOf #{:natlex/TestScan},
            :rdf/type
            #{:natlex/Entity :owl/Thing :natlex/ObservingAgent :rdfs/Resource},
            :natlex/integralTo #{:natlex/TestScan},
            :natlex/participantIn #{:natlex/TestScan}}
           ))

    (is (= (g :natlex/TestSpace)
           {:rdf/type #{:natlex/AbstractSpace :owl/Thing :rdfs/Resource},
            :natlex/relativeTo #{:natlex/TestEntity},
            :natlex/integralTo #{:natlex/TestEntity}}
           ))

    (is (= (g :natlex/TestTrajector)
           {:rdf/type #{:natlex/Entity :owl/Thing :rdfs/Resource},
            :natlex/primaryFigureOf #{:natlex/TestScan},
            :natlex/integralTo #{:natlex/TestScan},
            :natlex/participantIn #{:natlex/TestScan}}
           ))
))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Playing with population models
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def has-population-construct-query
  "
CONSTRUCT
{
  ?geographicRegion natlex:hasPopulation ?population.
}
WHERE
{
  {
    
    ?census a natlex:Census;
      natlex:assessedPopulatedArea ?geographicRegion;
      natlex:quantifiedAs ?population;
    .
  }
}
"
  ;; Values ?geographicRegion { $this }
  )

(defn get-population-rules
  "Returns rules for making inferences about population"
  []
  (-> (get-basic-rules)
      (add! [[:natlex/HasPopulationRuleShape
              :sh/description "Summarizes population assessment"
              :rdf/type :sh/NodeShape
              :sh/rule :natlex/HasPopulationRule
              ;;:sh/targetNode :sh/this
              :sh/targetClass :natlex/GeographicRegion
              :sh/deactivated false ;;true We could use this in a configuration layer.
              ]
             [:natlex/HasPopulationRule
              :rdf/type :sh/SPARQLRule
              :sh/construct (rdf/remove-newlines (rdf/prefixed has-population-construct-query))
              ] ])))

(defn apply-rule-model
  [source-graph rules-graph]
  (RuleUtil/executeRules (:model source-graph)
                         (:model rules-graph)
                         (:model source-graph)
                         nil)
  source-graph)

(defn get-seattle-census
  "Returns a graph about a Census of Seattle, with inferences from mini OWL and SHACL."
  []
  (let [g (reload)
        ]
    (add! g [[:natlex/Census
              :rdfs/subClassOf :natlex/Observation
              :rdfs/label "A observation of the population of some geographic region"]
             [:natlex/Population
              :rdfs/subClassOf :natlex/Magnitude]
             [:natlex/assessedPopulatedArea
              :rdfs/subPropertyOf :natlex/withSecondaryFigure
              :rdfs/domain :natlex/Census
              :rdfs/range :natlex/GeographicRegion]
             [:natlex/assessedPopulatedAreaOf
              :owl/inverseOf :natlex/assessedPopulatedArea]
             ;; [:natlex/PopulationOfSeattle :rdf/type :natlex/Population]
             [:natlex/assessedPopulation
              :rdfs/subPropertyOf :natlex/ofPrimaryFigure
              :rdfs/domain :natlex/Census
              :rdfs/range :Population]
             [:natlex/SeattleCensus
              :rdf/type :natlex/Census
              :natlex/byObserver :natlex/USCensusBureau
              :natlex/assessedPopulation :natlex/PopulationOfSeattle
              :natlex/assessedPopulatedArea :natlex/Seattle
              :natlex/quantifiedAs (voc/tag 737015)]             

             ])
    
    (let [new-content (-> (RuleUtil/executeRules (:model g)
                                                 (:model (get-population-rules))
                                                 nil
                                                 nil)
                          jena/make-jena-graph)
          ]
      #_ new-content
      (add! g (igraph/normal-form new-content))
      )))

(deftest test-seattle-census
  (let [g (get-seattle-census)
        ]
    (is (= {:natlex/hasPopulation 737015,
            :rdf/type
            #{:natlex/Entity
              :natlex/GeographicRegion
              :owl/Thing
              :rdfs/Resource},
            :natlex/integralTo :natlex/SeattleCensus,
            :natlex/assessedPopulatedAreaOf :natlex/SeattleCensus,
            :natlex/participantIn :natlex/SeattleCensus,
            :natlex/secondaryFigureOf :natlex/SeattleCensus}
           
           (igraph/flatten-description (g :natlex/Seattle))))
    
    (is (= {:rdfs/subClassOf
            #{:natlex/Population
              :natlex/AbstractSpatialElement
              :natlex/AbstractLocation
              :natlex/AbstractRegion
              :natlex/Magnitude
              :rdfs/Resource},
            :rdf/type #{:rdfs/Resource :rdfs/Class :owl/Class},
            :owl/equivalentClass #{:natlex/Population}}
           
           (g :natlex/Population)))))

(defn reload-temporality []
  "Returns an IGraph configured with an inferencer and populated with a schema"
  (let [im (->> (ModelFactory/createDefaultModel)
                (ModelFactory/createInfModel micro))
        ]
    ;; todo: infer loading based on :owl/imports
    (-> (jena/make-jena-graph im)
        (add-from-catalog! :nlx-ont/Top)
        (add-from-catalog! :nlx-ont/Characterization)
        (add-from-catalog! :nlx-ont/Temporality)
        )))

(defn do-temporality
  []
  (let [g (reload-temporality)
        ]
    (add! g [[:test/TestEvent
              :rdf/type :natlex/Event
              :natlex/hasAgent :test/TestAgent
              :natlex/hasPatient :test/TestPatient
              :natlex/hasStateTransition :test/TestTransition
              :natlex/hasDuration #voc/dstr "PT15S^^xsd:duration"
              :natlex/hasFinalState :test/TestFinalState
              ]
             [:test/TestProcess
              ;;:natlex/hasCharacteristicState :test/TestStateClass
              :natlex/hasSubEvent :test/TestEvent
              ]
             [:test/TestStateClass
              :rdfs/subClassOf :natlex/State
              ]])))

(voc/put-ns-meta! 'library
                  {:vann/preferredNamespacePrefix "library"
                   :vann/preferredNamespaceUri "http://example.com/library#"
                   })

(voc/put-ns-meta! 'library-instance
                  {:vann/preferredNamespacePrefix "eg"
                   :vann/preferredNamespaceUri "urn:eg:library:"
                   })

(voc/put-ns-meta! 'vcard
                  {:vann/preferredNamespacePrefix "vcard"
                   :vann/preferredNamespaceUri "http://www.w3.org/2006/vcard/ns#"
                   })

(voc/put-ns-meta! 'inference
                  {:vann/preferredNamespacePrefix "inference"
                   :vann/preferredNamespaceUri "http://rdf.naturallexicon.org/inference#"
                   })

(defn get-library-ontology
  []
  (let [g (reload-temporality)]
    (add-from-catalog! g :nlx-ont/Significance)
    (rdf/clear-url-cache! dataset-io-context)
    (rdf/read-rdf dataset-io-context g (io/resource "library.ttl"))
    ))

(defn get-library-process
  [g library]
  (unique (g library :library/hasManagementProcess)))

(defmethod mint-kwi :eg
  [_ & args]
  (voc/as-kwi (str (voc/as-uri-string "eg:") (clojure.string/join ":" args))))

;; PATRONS

(defn change-enrollment-status
  [g library patron enrollment-status time]
  (let [
        patron-id (unique (g patron :library/patronId))
        patron-name (unique (g patron :vcard/hasName))
        event-kwi (mint-kwi :eg "event:enroll" patron-name patron-id)
        process (get-library-process g library)
        enrollment-state (mint-kwi :eg "state:enrolled" patron-name patron-id)
        ]
    (add! g [[event-kwi
              :rdf/type :library/ToChangeEnrollmentStatus
              :library/actingLibrary library
              :library/affectedPatron patron
              :natlex/endTime time
              :natlex/hasFinalState enrollment-state
              ]
             [enrollment-state
              :rdf/type :library/EnrollmentState
              :library/hasEnrollmentStatus enrollment-status
              ]
             [process
              :natlex/hasSubEvent event-kwi
              ]])))

(defn enroll-patron!
  "Side-effect: adds patron with `patron-name` to `g` as a patron of `library` at `time`
  "
  [g library patron-name phone-number time]
  (let [patron-id (abs (hash (str library patron-name phone-number)))
        patron (mint-kwi :eg "patron" patron-name "id" patron-id)
        process (get-library-process g library)
        enrollment-state (mint-kwi :eg "state:enrolled" patron-name patron-id)
        ]
    (when (g patron :library/patronOf library)
      ;; We're making a simplifying assumption that all patron names are unique
      (throw (ex-info (str patron-name " has already been enrolled in " library)
                      {:type ::patron-has-already-been-enrolled
                       ::g g
                       ::patron-name patron-name
                       ::library library
                       })))
    (add! g [
             [patron
              :rdf/type :library/Patron
              :vcard/hasName patron-name
              :library/phoneNumber (voc/tag phone-number :library/Phone)
              :library/patronId patron-id
              :library/patronOf library
              ]])
    (change-enrollment-status g library patron :library/Enrolled time)))


;;  # Values (?patronName) { ( {{{ patron-name }}} ) }

#_(defn get-patron-id-query
  [patron-name]
  (prefixed
            (stache/render "
Select Distinct ?patron ?id
Where
{
  Values (?patronName) { ( {{{ patron-name }}} ) }
  ?patron rdfs:label ?patronName.
  ?patron library:patronId ?id.
}
"
                           {:patron-name (rdf/quote-str patron-name) }
                           )))


(defn get-patron-by-name
  [g patron-name]
  (-> (query g (flint-query '{:select [?patron ?id]
                              :where [[?patron :rdfs/label patron-name]
                                      [?patron :library/patronId ?id]]
                              })
             #_(get-patron-id-query patron-name))
      unique
      :patron))

;; Books

(defn add-person!
  "Returns `author`
  Side-effect: adds details for `author` to `g`"
  [g full-name & {:keys [q-name]}]
  (let [name-tokens (clojure.string/split full-name #"\s")
        given (first name-tokens)
        family (last name-tokens)
        ;; for this demo, we'll ignore middle names
        lookup (query g (flint-query `{:select [?author]
                                       :where [[?author :vcard/hasFamilyName ~family]
                                               [?author :vcard/hasGivenName ~given]
                                               [?author :vcard/hasName ~full-name]
                                               ]}))
        author (mint-kwi :eg "author" family given (count lookup))
        ]
    (add! g [[author
              :rdf/type :library/Person
              :vcard/familyName family
              :vcard/givenName given]
             ])
    (when q-name
      (add! g [author :library/wikidata q-name]))
    author
    ))

(defn add-book!
  "Returns `volume`
  Side-effect: adds `title` and `volume` detailst to `g`, relocates volume to `sheling`."
  [g library author title shelf-address & {:keys [q-number time] :or {time (now)}}]
  (let [the-hash (abs (hash {:author author
                             :title title
                             :shelf-address shelf-address
                             }))
        process (get-library-process g library)
        title_string (clojure.string/replace title #" " "_")
        title-uri (mint-kwi :eg "work" title_string the-hash)
        volume (mint-kwi :eg "volume" title_string the-hash)
        location (mint-kwi :eg (name volume) "shelf-location")
        volume-in-shelving (mint-kwi :eg "state" "in-shelving" title_string the-hash)
        volume-checked-in (mint-kwi :eg "state" "checked-in" title_string the-hash)
        to-ingest-volume (mint-kwi :eg "event" "ingest-volume" title_string the-hash)
        ]

    (add! g [title-uri
             :rdf/type :library/WrittenWork
             :library/hasAuthor author
             :rdfs/label title])
    (when q-number
      (add! g [title-uri :libary/wikidata q-number]))

    (add! g [[volume
              :rdf/type :library/Volume
              :library/ofWork title-uri
              :library/hasShelfLocation location]
             [location
              :rdf/type :library/ShelfLocation
              :library/inLibrary library
              :library/shelfAddress (voc/tag shelf-address :library/ShelfAddress)
              ]
             [to-ingest-volume
              :rdf/type :library/ToIngestVolume
              :library/actingLibrary library
              :library/affectedVolume volume
              :natlex/endTime time
              ]
             [process
              :natlex/hasSubEvent to-ingest-volume
              ]
             ]
          )
    volume))

(defn check-out-volume!
  [g library patron volume & {:keys [time] :or {time (now)}}]
  (assert patron)
  (assert volume)
  (assert (g patron :rdf/type :library/Person))
  (assert (g volume :rdf/type :library/Volume))
  (let [the-hash (abs (hash {:library library :patron patron :volume volume}))
        volume-name (unique (g volume (t-comp [:library/ofWork :rdfs/label])))
        event-kwi (voc/as-kwi (str "test:event:checkout:" volume-name the-hash))
        process (get-library-process g library)
        ]
    (add! g [[event-kwi
              :rdf/type :library/ToCheckOutVolume
              :library/actingLibrary library
              :library/affectedVolume volume
              :library/toVolumeLocation patron
              :natlex/endTime time
              ]
             ])))

(defn checkout-status-of-volume
  [g volume]
  (let [q (flint-query `{:select [?state ?status ?volume ?time]
                         :where [{?state
                                  {:rdf/type #{:library/CheckoutState}
                                   :library/ofVolume #{~volume}
                                   :library/hasCheckoutStatus #{?status}
                                   :natlex/atTime #{?time}
                                   }}]
                         :order-by [(~'desc ?time)]
                         :limit 1
                         })
        ]
    q
    (-> (igraph/query g q)
        unique
        :status)))


(defn check-in-volume!
  [g library volume & {:keys [time] :or {time (now)}}]

  (when (= (-> (checkout-status-of-volume g volume)
                      unique
                     :checkout)
           :library/CheckedIn)
    (throw (ex-info (str volume " is already checked in.")
                    {:type ::already-checked-in
                     ::g g
                     ::volume volume
                     })))
  (let [the-hash (abs (hash (str volume time)))
        volume-name (unique (g volume (t-comp [:library/ofWork :rdfs/label])))
        event-kwi (voc/as-kwi (str "test:event:checkin:" volume-name the-hash))
        process (get-library-process g library)
        ]
    (add! g [[event-kwi
              :rdf/type :library/ToCheckInVolume
              :library/actingLibrary library
              :library/affectedVolume volume
              :natlex/endTime time
              ]
             [process
              :natlex/hasSubEvent event-kwi
              ]])))

(defn get-shelf-location [g volume]
  (-> (g volume (t-comp [:library/hasShelfLocation :library/shelfAddress]))
      unique))

(defn shelve-volume!
  "Side-effect: locates `volume` at its associated location at `library` at `time` in `g`
  - Where
    - `g` is a graph model of `library`
    - `library` is the URI of the librarry being modeled
    - `volume` is the URI of the volume being shelved
    - `time` is an #inst indicating when the action was completed
  "
  [g library volume & {:keys [time] :or {time (now)}}]
  (let [the-hash (abs (hash (str library volume time)))
        event (mint-kwi :eg "event:shelve:" the-hash)
        process (get-library-process g library)
        location (-> (g volume :library/hasShelfLocation)
                     unique)
        ]
  (assert location)
  
  (add! g [[event
            :rdf/type :library/ToShelveVolume
            :library/actingLibrary library
            :library/affectedVolume volume
            :library/toVolumeLocation location
            :natlex/endTime time
            ]
           [process
            :natlex/hasSubEvent event
            ]])))
  

(defn where-is-volume
  [g volume]
  (let [q (flint-query
           `{:select [?location]
             :where [{?state {:library/ofVolume #{~volume}
                              :library/atVolumeLocation #{?location}
                              :natlex/atTime #{?time}}}]
             :order-by [(~'desc ?time)]
             :limit 1})]
    q
    (-> (igraph/query g q)
        unique
        :location
        )))

(defn lookup-by-name
  "Returns KWI in g matching 1abel"
  ([g label]
   (-> (query g (flint-query `{:select [?match]
                               :where [[?match  ~(list 'alt :rdfs/label :vcard/hasName) ~label]]
                               }))
       unique
       :match))
  ([g label on-ambiguity]
   (-> (query g (flint-query `{:select [?match]
                               :where [[?match (~'alt :rdfs/label :vcard/hasName) ~label]]
                               }))
       (unique on-ambiguity)
       :match)))

(defn title-volume
  "Returns a volume of the work indicated by `title` in `g`"
  [g title]
  (-> (lookup-by-name g title)
      (g :library/hasVolume)
      first))

(defn run-library
  []
  (let [g (get-library-ontology)
        ]
    (add! g [[:eg/MyLocalLibrary
              :library/hasManagementProcess :eg/MyLocalLibraryProcess
              ]])
    (enroll-patron! g :eg/MyLocalLibrary "Joe Smith"
                   (voc/tag "867-5309" :library/Phone)
                   #inst "2023-06-24")
    (let [author (add-person! g "John Steinbeck" :q-name :wd/Q39212)
          ]
      (add-book! g :eg/MyLocalLibrary author "East of Eden" "fiction|steinbeck john|east of eden|vol 1"))

    (let [author (add-person! g "Kurt Vonnegut")
          ]
      (add-book! g :eg/MyLocalLibrary author "Slaughterhouse 5" "fiction|vonnegut kurt|slaughterhouse 5|vol 1"))
    (check-out-volume! g
                       :eg/MyLocalLibrary
                       (lookup-by-name g "Joe Smith")
                       (title-volume g "Slaughterhouse 5")
                       )

    (enroll-patron! g :eg/MyLocalLibrary "Mary Jones" "555-0111" (now))
    (check-out-volume! g :eg/MyLocalLibrary
                       (lookup-by-name g "Mary Jones")
                       (title-volume g "East of Eden"))
    (check-in-volume! g
                      :eg/MyLocalLibrary
                      (title-volume g "Slaughterhouse 5"))

    (shelve-volume! g 
                    :eg/MyLocalLibrary
                    (title-volume g "Slaughterhouse 5"))
    ))

;;;;;;;;;;;
;; RULES
;;;;;;;;;;;

(defn list-rules
  "Returns a list of shacl rules defined in `g`"
  [g]
  (->>
   (query g (flint-query '{:select [?rule]
                           :where [[?rule :rdf/type :sh/SPARQLRule]]}))
   (map :rule)))

(def rule-order
  "Assigns each rule to a tier reflecting rule dependencies"
  [;; tier 0 -- do these first
   #{:inference/VolumeIsLocatedFromToChangeVolumeLocation
     :inference/CheckoutStateFromToChangeCheckoutStatus}
   ;; tier 1 -- follow-up
   #{:inference/FinalStateAtTimeFromEvent
     }])


(defn reorder-rules
  "Side-effect: assigns shacl rule priorities based on `rule-order`"
  [g]
  (dotimes [tier (count rule-order)]
    (doseq [rule (rule-order tier)]
      (when (g rule :sh/order)
        (subtract! g [rule :sh/order]))
      (add! g [rule :sh/order tier]))))

(defn enact-rules
  "Side:effect: applies the rules encoded in `g` and updates it with the results.
  "
  [g]
  ;; THE RULES ENGINE DOES NOT APPEAR TO HANDLE RULE ORDER PROPERLY
  ;; WHEN DEALING WITH NEWLY ADDED RESOURCES
  ;; WORK-AROUND SEEMS TO BE ENACTING EACH TIER IN SEQUENCE
  ;; THIS WORKS, BUT TAKES WAY TOO LONG.
  ;; SOMEWHERE THERE'S A BUNCH OF OVERHEAD
  ;;(reorder-rules g)
  (let [activate-tier (fn [g tier]
                        (dotimes [tier' (count rule-order)]
                          (doseq [rule (rule-order tier')]
                            (igraph/assert-unique!
                             g rule :sh/deactivated (not= tier' tier)))))
        ]
    (dotimes [tier (count rule-order)]
      (activate-tier g tier)
      (apply-rule-model g g))
    g))



;;;;;;;;;;;;;;;;;;
;; Significance
;;;;;;;;;;;;;;;;;;

(defn reload-significance []
  "Returns an IGraph configured with an inferencer and populated with a schema"
  (let [im (->> (ModelFactory/createDefaultModel)
                (ModelFactory/createInfModel micro))
        ]
    ;; todo: infer loading based on :owl/imports
    (-> (jena/make-jena-graph im)
        (add-from-catalog! :nlx-ont/Top)
        (add-from-catalog! :nlx-ont/Characterization)
        (add-from-catalog! :nlx-ont/Temporality)
        (add-from-catalog! :nlx-ont/Significance)
        )))

(defn get-java-code-ontology
  "Returns a graph describing java compilation as an extension of interpetation"
  []
  (let [g (reload-significance)]
    (add! g
          [;; global (add to characterization)
           [:test/JavaCompiler
            :rdfs/subClassOf :natlex/InterpretingAgent
            :rdfs/subClassOf :rdf/_:interpreter-for-java
            :dc/description "Extends to a running process that interprets java code."
            :rdfs/comment "Relationship of this process to the program that defines the compiler is left implicit"
            ]
           [:rdf/_:interpreter-for-java
            :owl/onProperty :natlex/interpreterFor
            :owl/allValuesFrom :test/JavaLanguage
            ]
           [:test/JavaProgram
            :rdfs/subClassOf :test/ComputerProgram
            :owl/subClassOf :rdf/_:language-is-java
            ]
           [:rdf/_:language-is-java
            :owl/onProperty :test/computerLanguage
            :owl/allValuesFrom :test/JavaLanguage
            :dc/description "computer language is Java"
            ]
           [:test/JavaLanguage
            :rdfs/subClassOf :test/ComputerLanguage
            :dc/description "Extends to a specfic version of Java."
            ]
           [:test/ComputerLanguage
            :rdfs/subClassOf :natlex/SystemOfSigns
            :dc/description "A computer language a system of signs used by an interpreting agent to produce executable content."
            ]
           [:test/Java_v_17
            :rdf/type :test/JavaLanguage
            :dc/description "Version 17 of Java"
            ]
           [:test/MyJavaProject
            :rdf/type :test/JavaProgram
            :test/url (java.net.URL. "file:///path/to/my/project")
            :rdfs/label "my-java-program"
            :test/computerLanguage :test/Java_v_17
            ]
           [:test/MyOS :rdf/type :test/OperatingSystem
            :test/hasInstalled :test/MyJavaCompiler
            ]
           [:test/MyJavaCompiler
            :rdf/type :test/JavaCompiler
            :test/url (java.net.URL. "file:///path/to/my/java/compiler")
            ]
           [:test/JarFile
            :rdfs/subClassOf :test/ComputerProgram
            :rdfs/subClassOf :rdf/_:language-is-jvm-executable
            ]
           [:rdf/_:language-is-jvm-executable
            :owl/onProperty :test/computerLanguage
            :owl/hasValue :test/JVMExecutable
            ]
           [:test/JVMExecutable
            :dc/description "A program interpretable by java RTE"
            ]
           ]
          )))

(defn compile-project
  [g java-project]

  (let [compile-event (str (voc/as-uri-string "test:")
                           "compile-event:"
                           (clojure.core/random-uuid))
        jar-file (java.net.URL. "file:///path/to/my/project/my-project.jar")
        compiler-q (flint-query
                    '{:select [?compiler]
                      :where [[?operatingSystem :rdf/type :test/OperatingSystem]
                              [?operatingSystem :test/hasInstalled ?compiler]
                              [?compiler :rdf/type :test/JavaCompiler]]
                      })
        compiler (-> (query g compiler-q)
                     unique
                     :compiler)
        
        ]
    (add! g [[compile-event
              :rdf/type :test/CompileEvent
              :test/compiler compiler
              :test/output jar-file
              ]
             [jar-file :rdf/type :test/JarFile
              :test/url (voc/as-uri-string jar-file)
              ]
             ])
    ))

(defn get-library-catalog-ontology []
  "Returns an IGraph configured with an inferencer and populated with a schema"
  (let [g     (-> (get-library-ontology)
                  (add-from-catalog! :nlx-ont/Intentionality)
                  )
        ]
    (add! g [[:OnlineLibraryCatalog
              :rdfs/subClassOf :natlex/Entity
              :natlex/hasTypicalPurpose :test/UserKnowsLibraryContent
              ]
             [:test/KnowledgeSpace
              :rdfs/subClassOf :natlex/Reality
              :dc/description "Extends to a space defined relative to a specific observer we may call the 'knower'. Regions in this space correspond to actual or potential knowledge. Regions within this space may be the intensions of concepts referenced as classes, and may be describable by signs."
              ]
             [:test/knower
              :rdfs/subPropertyOf :natlex/accordingTo
              ]
             [:test/UserKnowsAboutLibrary
              :rdfs/subClassOf :test/KnowledgeState
              :rdfs/subClassOf :rdf/_:knower-is-patron
              :rdfs/subClassOf :rdf/_:known-is-about-libary
              :rdfs/comment "A state wherein a region a patron's knowledge space specifyable by a knowledge description is within the region of actuality within that space."
              ]
             [:rdf/_:knower-is-patron
              :owl/onProperty :test/knower
              :owl/allValuesFrom :test/Patron
              ]
             [:rdf/_:known-is-about-libary
              :owl/onProperty :test/known
              :owl/someValuesFrom :test/KnowledgeAboutLibrary
              ]             
             [:test/KnowledgeAboutLibrary
              :rdfs/subClassOf :natlex/AbstractRegion
              :dc/description "Extends to a region in a knowledge space containing knowledge of some topic."
              ]
             [:test/forLibrary
              :rdfs/domain :test/KnowledgeAboutLibrary
              :rdfs/range :test/Library
              :dc/description "Asserts the library whose contents we are identifying contents of."
              ]
             [:test/LibraryContentDescription
              :rdfs/subClassOf :natlex/Sign
              :rdfs/subClassOf :rdf/_:signifies-some-knowledge-of-library-contents
              :dc/description "Extends to descriptions of some sub-region of knowledge of library contents"
              ]

             ])))




(defn test-bnodes
  []
  (let [g (jena/make-jena-graph)]
    (add! g [[:rdf/_:test :rdf/type :natlex/Entity]])
    g))

;;;;;;;;;;;;;;;;;;;;;;;;
;; FUSEKI/SPARQL CLIENT
;;;;;;;;;;;;;;;;;;;;;;;;
(defn launch-server-with-dataset
  "Side-effect: launches a server for `g` on `port
  Returns: `m` s.t. (keys m) :~#{:builder :server :client}
  "
  [g port]
  (let [graph-name :natlex/Ontology
        dataset (doto (DatasetFactory/create)
                  (.addNamedModel (voc/as-uri-string graph-name)
                                  (:model g)))
        
        fuseki-builder (doto (FusekiServer/create)
                        (.port port)
                        (.add "ds/" dataset true) ;; true for read-only
                        (.build))
        ]
    
    {:builder fuseki-builder
     :server (.start fuseki-builder) ;; this publishes it to localhost:3033
     :client (sparql-client/make-sparql-updater
              :graph-uri graph-name
              :query-url (format "http://localhost:%s/ds/sparql"port)
              :update-url (format "http://localhost:%s/ds/update" port)
              )
     }))

(defn start-server
  [server]
  (-> server
      :server
      (.start)))

(defn stop-server
  [server]
  (-> server
      :server
      (.stop)))

;;;;;;;;;;;;;;;;;;
;; Use reflection
;;;;;;;;;;;;;;;;;;

(defn describe-api
  "Returns [`member`, ...] for `obj`, sorted by :name,  possibly filtering on `name-re`
  - Where
    - `obj` is an object subject to reflection
    - `name-re` is a regular expression to match against (:name `member`)
    - `member` := m, s.t. (keys m) = #{:name, :parameter-types, :return-type}
  "
  ([obj]
   (let [collect-public-member (fn [acc member]
                                (if (not
                                     (empty?
                                      (clojure.set/intersection #{:public}
                                                                (:flags member))))
                                  (conj acc (select-keys member [:name :parameter-types :return-type]))
                                  ;;else member is not public
                                  acc))
        ]
     (sort (fn compare-names [this that] (compare (:name this) (:name that)))
           (reduce collect-public-member [] (:members (reflect obj))))))
  ([obj name-re]
   (filter (fn [member]
             (re-matches name-re (str (:name member))))
           (describe-api obj))))
          


(def TestDTMetaMap (atom {}))

(deftype TestDT1 [s metadata]
  Object
  (hashCode [this] (hash (str (.s this) "@" (.datatype this))))
  (toString [_] s)
  (equals [this that]
       (and (instance? TestDT1 that)
            (= (.s this) (.s that))))
  clojure.lang.IMeta
  (meta [this]
    (or (@metadata this)
        {}))
  #_(with-meta [this m]
    (reset! (.metadata this) m)))

(comment
  (def dataset (doto (DatasetFactory/create)
                 (.addNamedModel 
                  (voc/as-uri-string :natlex/Ontology)
                  (:model g))))
  
  (def fuseki-server (doto (FusekiServer/create)
                            (.port 3033)
                            (.add "ds/" dataset)
                            (.build)))
  
  (.start fuseki-server) ;; this publishes it to localhost:3033

  (sparql-client/make-sparql-reader
   :graph-uri :natlex/Ontology
   :query-url "http://localhost:3033/ds/sparql")

  (count (subjects endpoint))
  ;; -> 184

  (def x
    (.listStatements (:model g)
                     (.createResource (:model g) (voc/as-uri-string :natlex/Action))
                     (.createProperty (:model g) (voc/as-uri-string :rdf/type))
                     nil))

  )

  
                                           


  (comment
  (def q "
SELECT *
WHERE
{
  ?event a library:ToChangeCheckoutStatus.
  FILTER NOT EXISTS
  {
    ?event natlex:hasFinalState [a natlex:CheckoutState].
  }
  BIND (URI (CONCAT (STR (?event), ':finalState:CheckoutStatus')) AS ?state)
  ?event
    library:actingLibrary ?library;
    library:affectedVolume ?volume;
  .
}
  "))
