/* eslint-disable */
/**
 * Created by Spadon on 13/11/2015.
 */

const Logics = require("./Logics/Logics");

/**
 * Dictionary used to index triples (in turtle) and their fact representation.
 * @type {{substractFactSets: Function, combine: Function}|exports|module.exports}
 */

const Utils = require('./Utils')
const ParsingInterface = require('./ParsingInterface')
const Fact = require('./Logics/Fact');
const Rule = require('./Logics/Rule');

function Dictionary(dict, index) {
    this.dict = dict || {
        '#default': {}
    };
    this.lastUpdate = 0;
    this.purgeThreshold = 13000000;

    // index
    this.index = index || {
        "#default": {
            predicate: {
                subject: {
                    object: null
                }
            }
        }
    }
};

Dictionary.clone = function (dict) {
    const _dict = new Dictionary();
    Object.assign(_dict, dict);
    return _dict;
};

Dictionary.fromFacts = function(facts) {
    const dict = new Dictionary();
    for (let i=0; i < facts.length; i++) {
        dict.put(facts[i],graph);
    }
    return dict;
}

/**
 * Checks if an object is an instance of Dictionary
 * @param {*} obj - The object to check
 * @returns {boolean} - True if obj is a Dictionary instance, false otherwise
 */
Dictionary.isDictionary = function(obj) {
    if (!obj || typeof obj !== 'object') return false;

    // Check for required instance methods
    const requiredMethods = [
        'clone',
        'turnOnForgetting',
        'turnOffForgetting',
        'resolveGraph',
        'clear',
        'get',
        'put',
        'putIndex',
        'getIndex'
    ];

    return requiredMethods.every(method =>
        typeof obj[method] === 'function'
    ) && obj.dict !== undefined && obj.index !== undefined;
};

/**
 * Return a copy of this dictionary.
 * Facts are copied by reference, but the dict is independent,
 * and thus adds and deletions do not affect the original.
 * @returns {Dictionary}
 */
Dictionary.prototype.clone = function() {
    const clone = new Dictionary();
    // graphs
    for (const graph of Object.keys(this.dict)) {
        const facts = this.values(graph);
        for (let i=0; i < facts.length; i++) {
            clone.put(facts[i],graph);
        }
    }
    return clone;
};

Dictionary.prototype.turnOnForgetting = function() {
    this.allowPurge = true;
};

Dictionary.prototype.turnOffForgetting = function() {
    this.allowPurge = false;
};

Dictionary.prototype.resolveGraph = function(graph = '#default') {
    if (!this.dict[graph]) {
        this.dict[graph] = {};
    }
    return graph;
};

Dictionary.prototype.clear = function() {
    this.dict = {
        '#default': {}
    };
};

/**
 * Returns the fact corresponding to the turtle triple.
 * @param ttl
 * @returns {Fact[]|false}
 */
Dictionary.prototype.get = function(ttl, graph) {
    var facts;
    graph = this.resolveGraph(graph);
    facts = this.dict[graph][ttl];
    if (facts !== undefined) {
        return facts;
    }
    else return false;
};

/**
 * Updates the fact representation of
 * an existing turtle triple, or puts
 * a new one by transform the fact into turtle
 * through the ParsingInterface.
 * @param {Fact} fact
 * @returns {true|Error}
 */
Dictionary.prototype.put = function(fact, graph) {
    var timestamp = new Date().getTime(), factToTurtle;

    if (this.allowPurge) {
        this.purgeOld();
    }

    this.lastUpdate = timestamp;
    graph = this.resolveGraph(graph);

    try {
        // 2wav experiment... reasoner has created facts
        // with literal subjects, e.g. "The Friend of a Friend (FOAF) RDF vocabulary, described using W3C RDF Schema and the Web Ontology L      anguage."^^<http://www.w3.org/2001/XMLSchema#string> <http://www.w3.org/1999/02/22-rdf-syntax-ns#typ      e> <http://www.w3.org/2001/XMLSchema#string> .
        if (fact.subject.indexOf(`"`) === 0) {
            // console.log("skip Fact with literal subject", fact.subject);
            return;
        }
        if(fact.predicate === 'FALSE') {
            this.dict[graph]['__FALSE__'] = [fact];
        } else {
            factToTurtle = ParsingInterface.factToTurtle(fact);
            if (this.dict[graph][factToTurtle]) {
                this.dict[graph][factToTurtle] = Utils.insertUnique(this.dict[graph][factToTurtle], fact);
            } else {
                this.dict[graph][factToTurtle] = [fact];
                this.dict[graph][factToTurtle].lastUpdate = timestamp;
            }
        }
        this.putIndex(fact,graph);
        return true;
    } catch(e) {
        return e;
    }
};

/**
 * Put a fact into hash index.
 * @param {Fact} fact
 * @param {string} [graph="#default"]
 * @returns {Fact[]}
 */
Dictionary.prototype.putIndex = function(fact, graph) {
    graph = this.resolveGraph(graph);
    this.index[graph] = this.index[graph] ?? {};
    // predicate
    this.index[graph][fact.predicate] = this.index[graph][fact.predicate] ?? {};
    this.index[graph][fact.predicate][fact.subject] = this.index[graph][fact.predicate][fact.subject] ?? {};
    const o = fact.object.toString();
    this.index[graph][fact.predicate][fact.subject][o] = this.index[graph][fact.predicate][fact.subject][o] ?? {};
    this.index[graph][fact.predicate][fact.subject][o] = fact;
}

/**
 * Pull all matching facts from index.
 * Params which are query variables like ?x will match all.
 *
 * @param {string} s
 * @param {string} p
 * @param {string} o
 * @param {string} [graph="#default"]
 * @returns {Fact[]}
 */
Dictionary.prototype.getIndex = function(s,p,o,graph) {
    s = s ?? "";
    p = p ?? "";
    o = o ?? "";
    graph = this.resolveGraph(graph);
    const facts = [];
    const ps = (p[0] === "?") ? Object.keys(this.index[graph]) : [p];
    for (const _p of ps) {
        if (this.index[graph][_p]) {
            const ss = (s[0] === "?") ? Object.keys(this.index[graph][_p]) : [s];
            for (const _s of ss) {
                if (this.index[graph][_p][_s]) {
                    const os = (o[0] === "?") ? Object.keys(this.index[graph][_p][_s]) : [o];
                    for (const _o of os) {
                        if (this.index[graph][_p][_s][_o]) {
                            const f = this.index[graph][_p][_s][_o];
                            facts.push(f);
                        }
                    }
                }
            }
        }
    }
    return facts;
};

Dictionary.prototype.isOld = function(graph, factIndex) {
    return (this.dict[graph][factIndex].lastUpdate - this.lastUpdate) > this.purgeThreshold;
};

Dictionary.prototype.purgeOld = function() {
    for (var i in this.dict.length) {
        for (var j in this.dict[i].length) {
            for (var k in this.dict[i][j]) {
                if (!this.dict[i][j][k].isValid() && this.isOld(i,j)) {
                    delete this.dict[i][j][k];
                }
            }
        }
    }
};

/**
 * Return the full content of the dictionary.
 * @returns {Object}
 */
Dictionary.prototype.content = function() {
    return this.dict;
};

/**
 * Sets dictionary's content.
 * @param content Object
 */
Dictionary.prototype.setContent = function(content) {
    this.dict = content;
};

/**
 * Gets all facts from the dictionary.
 * @returns {Array}
 */
Dictionary.prototype.values = function(graph) {
    var values = [];
    graph = this.resolveGraph(graph);
    for (var key in this.dict[graph]) {
        for (var i = 0; i < this.dict[graph][key].length; i++) {
            values.push(this.dict[graph][key][i]);
        }
    }
    return values;
};

/**
 * Get all explicit facts from full dictionary graph as turtle.
 * @returns {Array}
 */
Dictionary.prototype.explicitGraphs = function(graph) {
    let explicitGraphs = []
    for (let graph in this.dict) {
        explicitGraphs.push({
            name: graph,
            content: ParsingInterface.factsToTurtle(Logics.getOnlyExplicitFacts(this.values(graph)))
        })
    }
    return explicitGraphs
}

/**
 * Get all all facts from full dictionary graph as turtle.
 * @returns {Array}
 */
Dictionary.prototype.allGraphsAsTtl = function(graph) {
    let allTriples = []
    for (let graph in this.dict) {
        allTriples.push({
            name: graph,
            content: ParsingInterface.factsToTurtle(this.values(graph))
        })
    }
    return allTriples
}

/**
 * Gets facts corresponding to the turtle triples,returns an object
 * {found: facts found, notfound: turtle triples with no repr.}
 * @param triples An array of turtle triples.
 * @returns {{found: Array, notfound: Array}}
 */
Dictionary.prototype.findValues = function(triples = [], graph) {
    var values = [], notfound = [],
        facts;
    graph = this.resolveGraph(graph);
    for (var i = 0; i < triples.length; i++) {
        facts = this.dict[graph][triples[i].toString().slice(0, -2)];
        if(facts !== undefined) {
            for (var j = 0; j < facts.length; j++) {
                values.push(facts[j]);
            }
        } else {
           notfound.push(triples[i]);
        }
    }
    return {
        found: values,
        notfound: notfound
    };
};

/**
 * Gets turtle triples corresponding to the facts,returns an object
 * {found: triples found, notfound: facts repr. nothing.}
 * @param values
 * @returns {{found: Array, notfound: Array}}
 */
Dictionary.prototype.findKeys = function(values, graph) {
    var keys = [], value, notfound = [];
    graph = this.resolveGraph(graph);
    for (var i = 0; i< values.length; i++) {
        value = values[i];
        for (var key in this.dict[graph]) {
            try {
                if (this.dict[graph][key].toString().indexOf(value.toString()) !== -1) {
                    keys.push(key);
                    break;
                } else {
                    notfound.push(value);
                }
            } catch(e) {
                throw e;
            }
        }
    }
    return {
        found: keys,
        notfound: notfound
    };
};

Dictionary.prototype.getFactFromStringRepresentation = function(factStr, graph) {
    graph = this.resolveGraph(graph);
    for (var key in this.dict[graph]) {
        for (var i = 0; i < this.dict[graph][key].length; i++) {
            if (this.dict[graph][key][i].toString() == factStr) {
                return {
                    key: key,
                    value: this.dict[graph][key][i],
                    graph: graph
                };
            }
        }
    }
    return false;
}

Dictionary.prototype.flatten = function() {
    const resultMap = new Map();
    let factIdCounter = 0;
    let ruleIdCounter = 0;

    // Process each graph in the dictionary
    for (const graphUri in this.dict) {
        const graphMap = new Map();
        resultMap.set(graphUri, graphMap);
        const processedObjects = new Set(); // Track processed objects to avoid cycles
        const objectMap = new Map(); // Map to store original objects by their IDs

        // Use a queue for iterative traversal instead of recursion
        const queue = [];

        // Add only the dictionary structure to the queue
        queue.push(this.dict[graphUri]);

        // First pass: assign IDs to all Fact and Rule objects
        while (queue.length > 0) {
            const obj = queue.shift();

            // Skip if null, undefined, or already processed
            if (!obj || typeof obj !== 'object' || processedObjects.has(obj)) {
                continue;
            }

            // Mark as processed to avoid cycles
            processedObjects.add(obj);

            // Handle Fact instances
            if (obj instanceof Fact) {
                // Skip facts with literal subjects
                if (obj.subject && obj.subject.indexOf(`"`) === 0) {
                    continue;
                }

                // Assign a unique ID if not already assigned
                if (!obj._id) {
                    obj._id = `fact_${factIdCounter++}`;
                }
                // Assign graphUri if not already assigned
                if (!obj.graphs.includes(graphUri)) {
                    obj.graphs.push(graphUri);
                }

                // Add type property
                obj._type = 'Fact';

                // Store the original object in the map
                objectMap.set(obj._id, obj);

                // Add all properties to the queue for further processing
                for (const key in obj) {
                    if (Object.prototype.hasOwnProperty.call(obj, key) && key !== '_id' && key !== '_type') {
                        queue.push(obj[key]);
                    }
                }
                continue;
            }

            // Handle Rule instances
            if (obj instanceof Rule) {
                // Assign a unique ID if not already assigned
                if (!obj._id) {
                    obj._id = `rule_${ruleIdCounter++}`;
                }
                // Assign graphUri if not already assigned
                if (!obj.graphs.includes(graphUri)) {
                    obj.graphs.push(graphUri);
                }
                // Add type property
                obj._type = 'Rule';

                // Store the original object in the map
                objectMap.set(obj._id, obj);

                // Add all properties to the queue for further processing
                for (const key in obj) {
                    if (Object.prototype.hasOwnProperty.call(obj, key) && key !== '_id' && key !== '_type') {
                        queue.push(obj[key]);
                    }
                }
                continue;
            }

            // Handle arrays
            if (Array.isArray(obj)) {
                for (let i = 0; i < obj.length; i++) {
                    queue.push(obj[i]);
                }
                continue;
            }

            // Handle Maps
            if (obj instanceof Map) {
                for (const [key, value] of obj.entries()) {
                    queue.push(value);
                }
                continue;
            }

            // For regular objects, add all properties to the queue
            for (const key in obj) {
                if (Object.prototype.hasOwnProperty.call(obj, key)) {
                    queue.push(obj[key]);
                }
            }
        }

        // Second pass: create flattened objects with references replaced by {_id, _type}
        processedObjects.clear();
        queue.length = 0;
        queue.push(this.dict[graphUri]);

        // Process all objects in the objectMap to create flattened versions
        for (const [id, obj] of objectMap.entries()) {
            // Create a flattened copy of the object
            const flattenedObj = { ...obj };

            // Add to graph map
            graphMap.set(id, flattenedObj);

            // Process all properties to replace references
            for (const key in flattenedObj) {
                if (Object.prototype.hasOwnProperty.call(flattenedObj, key) && key !== '_id' && key !== '_type') {
                    const value = flattenedObj[key];

                    // Replace Fact or Rule references with {_id, _type} objects
                    if (value instanceof Fact || value instanceof Rule) {
                        flattenedObj[key] = { _id: value._id, _type: value._type };
                    } else if (Array.isArray(value)) {
                        // Handle arrays of Facts or Rules
                        flattenedObj[key] = value.map(item => {
                            if (item instanceof Fact || item instanceof Rule) {
                                return { _id: item._id, _type: item._type };
                            }
                            return item;
                        });
                    } else if (typeof value === 'object' && value !== null) {
                        // Handle nested objects - recursively flatten them
                        const flattenedNested = {};
                        for (const nestedKey in value) {
                            if (Object.prototype.hasOwnProperty.call(value, nestedKey)) {
                                const nestedValue = value[nestedKey];
                                if (nestedValue instanceof Fact || nestedValue instanceof Rule) {
                                    flattenedNested[nestedKey] = { _id: nestedValue._id, _type: nestedValue._type };
                                } else if (Array.isArray(nestedValue)) {
                                    flattenedNested[nestedKey] = nestedValue.map(item => {
                                        if (item instanceof Fact || item instanceof Rule) {
                                            return { _id: item._id, _type: item._type };
                                        }
                                        return item;
                                    });
                                } else {
                                    flattenedNested[nestedKey] = nestedValue;
                                }
                            }
                        }
                        flattenedObj[key] = flattenedNested;
                    }
                }
            }
        }
    }

    return resultMap;
}

Dictionary.prototype.loadMap = function(map, opts) {
    opts = opts || {};
    opts.reload = opts.reload !== false;
    if (opts.reload) {
        this.dict = dict || {
            '#default': {}
        };
        this.index = index || {
            "#default": {
                predicate: {
                    subject: {
                        object: null
                    }
                }
            }
        }
    }
    for (const [graphUri, graphMap] of map.entries()) {
        console.log(`${graphUri} graphMap has ${graphMap.size} entries`);
        // First pass: populate objectMap with all objects converted to instances
        const objectMap = new Map();
        for (const [id, obj] of graphMap.entries()) {
            let replacement;
            switch (obj._type) {
                case "Fact":
                    if (!Fact.isFact(obj)) {
                        replacement = Fact.clone(obj);
                    }
                    break;
                case "Rule":
                    if (!Rule.isRule(obj)) {
                        replacement = Rule.clone(obj);
                    }
                    break;
                case "Dictionary":
                    if (!Dictionary.isDictionary(obj)) {
                        replacement = Dictionary.clone(obj);
                    }
                    break;
                default:
            }
            if (replacement) {
                objectMap.set(id, replacement);
            }
            else {
                objectMap.set(id, obj);
            }
        }
        console.log(`${graphUri} objectMap has ${objectMap.size} entries`);

        // next pass: replace all {_id, _type} references with actual instances
        // Use a queue-based approach to avoid recursion and potential stack overflow
        const queue = [];
        const processedObjects = new Set();

        // Add all instances to the queue for processing
        for (const [id, instance] of objectMap.entries()) {
            queue.push(instance);
        }

        // Process all objects in the queue
        while (queue.length > 0) {
            const obj = queue.shift();
            // Skip if null, undefined, or already processed
            if (!obj || typeof obj !== 'object' || processedObjects.has(obj)) {
                continue;
            }

            // Mark as processed to avoid cycles
            processedObjects.add(obj);

            // Process all properties of the object
            for (const key in obj) {
                if (Object.prototype.hasOwnProperty.call(obj, key)) {
                    const value = obj[key];

                    // Replace {_id, _type} references with actual instances
                    if (value && typeof value === 'object' && value._id && value._type) {
                        let replacement;
                        const pojo = objectMap.get(value._id);
                        if (pojo) {
                            switch (value._type) {
                                case "Fact":
                                    replacement = Fact.clone(pojo);
                                    break;
                                case "Rule":
                                    replacement = Rule.clone(pojo);
                                    break;
                                case "Dictionary":
                                    replacement = Dictionary.clone(pojo);
                                    break;
                                default:
                            }
                        }
                        if (replacement) {
                            obj[key] = replacement;
                        }
                    } else if (Array.isArray(value)) {
                        // Handle arrays of references
                        for (let i = 0; i < value.length; i++) {
                            const item = value[i];
                            if (item && typeof item === 'object') {
                                // Process the item directly instead of pushing it to the queue
                                // This ensures changes are reflected in the array
                                if (item._id && item._type) {
                                    let replacement;
                                    const pojo = objectMap.get(item._id);
                                    if (pojo) {
                                        switch (item._type) {
                                            case "Fact":
                                                replacement = Fact.clone(pojo);
                                                break;
                                            case "Rule":
                                                replacement = Rule.clone(pojo);
                                                break;
                                            case "Dictionary":
                                                replacement = Dictionary.clone(pojo);
                                                break;
                                            default:
                                        }
                                    }
                                    if (replacement) {
                                        value[i] = replacement;
                                    }
                                }
                                // Still add the item to the queue for further processing
                                queue.push(value[i]);
                            }
                        }
                    } else if (typeof value === 'object' && value !== null) {
                        // Add nested objects to the queue for processing
                        queue.push(value);
                    }
                }
            }
        }

        // Fourth pass: add instances to the dictionary using this.put
        for (const [id, instance] of objectMap.entries()) {
            if (Fact.isFact(instance)) {
                this.put(instance, graphUri);
            }
        }
    }

    return this;
};

module.exports = Dictionary;
