/* eslint-disable */
/**
 * Created by Spadon on 13/11/2015.
 */

const Logics = require("./Logics/Logics");

/**
 * Dictionary used to index triples (in turtle) and their fact representation.
 * @type {{substractFactSets: Function, combine: Function}|exports|module.exports}
 */

const fs = require("fs");
const _ = require("lodash");
const Utils = require('./Utils');
const ParsingInterface = require('./ParsingInterface');
const Fact = require('./Logics/Fact');
const Rule = require('./Logics/Rule');

function Dictionary(dict, index) {
    this._type = "Dictionary";
    this._id = `dict_${Date.now()}`;
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

    // Each Rule and Facts which are Causes have a _seen hash which
    // notes the facts previously seen and therefore do not need to be Solved again.
    // Those _seen collections can be quite large, so they are not persisted
    // in saveToCollection.
    // After loadFromCollection, I think that all Rules and Causes can be said
    // to have seen all Facts. Only new ones need to be added to the specific Fact|Rule._seen
    // update: I think this may hold true only during initial classify...
    this._seen = new Set();

    // Incremental graph hash (two 32-bit accumulators, xor of per-fact hashes).
    // Solver consults `graphHash` getter to early-out when the dict is unchanged
    // since a cause last looked at it.
    this._graphHash0 = 0;
    this._graphHash1 = 0;

};

/**
 * FNV-1a-style 32-bit hash, seedable so we can derive two independent
 * lanes for an effective 64-bit fact identifier. Cached on the Fact as `_hash`.
 */
function _factHashLane(str, seed) {
    let h = seed | 0;
    for (let i = 0; i < str.length; i++) {
        h = Math.imul(h ^ str.charCodeAt(i), 0x01000193);
    }
    return h >>> 0;
}

function _factHash(fact) {
    if (fact._hash !== undefined) return fact._hash;
    const s = fact.asString;
    fact._hash = [_factHashLane(s, 0x811c9dc5), _factHashLane(s, 0x9dc58119)];
    return fact._hash;
}

Object.defineProperty(Dictionary.prototype, 'graphHash', {
    get() {
        const h0 = this._graphHash0 >>> 0;
        const h1 = this._graphHash1 >>> 0;
        return `${h0.toString(16)}:${h1.toString(16)}`;
    },
    configurable: true,
});

Dictionary.prototype._xorFact = function(fact) {
    const [h0, h1] = _factHash(fact);
    this._graphHash0 = (this._graphHash0 ^ h0) >>> 0;
    this._graphHash1 = (this._graphHash1 ^ h1) >>> 0;
};

Dictionary.clone = function (dict) {
    const _dict = new Dictionary();
    Object.assign(_dict, dict);
    return _dict;
};

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
    clone._seen = this._seen;
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
    this._graphHash0 = 0;
    this._graphHash1 = 0;
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
            const existed = !!this.dict[graph]['__FALSE__'];
            this.dict[graph]['__FALSE__'] = [fact];
            if (!existed) this._xorFact(fact);
        } else {
            factToTurtle = ParsingInterface.factToTurtle(fact);
            if (this.dict[graph][factToTurtle]) {
                const arr = this.dict[graph][factToTurtle];
                const prevLen = arr.length;
                const updated = Utils.insertUnique(arr, fact);
                this.dict[graph][factToTurtle] = updated;
                // insertUnique replaces by asString-key; only a length increase
                // means the dict gained a new asString.
                if (updated.length > prevLen) {
                    this._xorFact(fact);
                }
            } else {
                this.dict[graph][factToTurtle] = [fact];
                this.dict[graph][factToTurtle].lastUpdate = timestamp;
                this._xorFact(fact);
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
                const fact = this.dict[i][j][k];
                if (!fact.isValid() && this.isOld(i,j)) {
                    this._xorFact(fact);
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

/**
 * CAUTION: useful for testing small dicts, dangerous on large ones.
 * @return {string}
 */
Dictionary.prototype.toString = function() {
    var obj = {};
    for (var graph in this.dict) {
        obj[graph] = obj[graph] || {};
        for (var key in this.dict[graph]) {
            obj[graph][key] = obj[graph][key] || [];
            for (var i = 0; i < this.dict[graph][key].length; i++) {
                obj[graph][key].push(this.dict[graph][key][i].toString());
            }
        }
    }
    return JSON.stringify(obj,null,2);
};

/**
 * @deprecated _This major effort appears to be a failure. The restored reasoner
 * doesn't find expected inferences. The use of a globally seen Fact Set appears
 * to be the problem._
 *
 * @param {MongoDB.Collection} collection
 * @return {Promise<void>}
 */
Dictionary.prototype.saveToCollection = async function(collection) {
    if (!collection) {
        throw new Error("Collection is required for saveToCollection");
    }

    // Clear the collection first
    await collection.drop().catch(err => {
        // Ignore error if collection doesn't exist
        if (err.code !== 26) {
            console.error("Error dropping collection:", err);
        }
    });

    let factIdCounter = 0;
    let ruleIdCounter = 0;
    const processedObjects = new Set(); // Track processed objects to avoid cycles
    const objectMap = new Map(); // Map to store original objects by their IDs

    // Process each graph in the dictionary
    for (const graphUri in this.dict) {
        const queue = [];
        queue.push(this.dict[graphUri]);

        // First pass: assign IDs to all Fact and Rule objects
        while (queue.length > 0) {
            if (queue.length % 100 === 0) {
                console.log(`${queue.length} objects in queue to process`);
            }
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

                // Add all object properties to the queue for further processing
                // this covers arrays too.
                for (const key in obj) {
                    if (Object.prototype.hasOwnProperty.call(obj, key) &&
                      key !== '_id' &&
                      key !== '_type' &&
                      obj[key] !== null &&
                      typeof obj[key] === 'object'
                    ) {
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

                // Add all object properties to the queue for further processing
                // this covers arrays too.
                for (const key in obj) {
                    if (Object.prototype.hasOwnProperty.call(obj, key) &&
                      key !== '_id' &&
                      key !== '_type' &&
                      obj[key] !== null &&
                      typeof obj[key] === 'object'
                    ) {
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

            // For regular objects,
            // Add all object properties to the queue for further processing
            // this covers arrays too.
            for (const key in obj) {
                if (Object.prototype.hasOwnProperty.call(obj, key) &&
                  key !== '_id' &&
                  key !== '_type' &&
                  obj[key] !== null &&
                  typeof obj[key] === 'object'
                ) {
                    queue.push(obj[key]);
                }
            }
        }

        // Second pass: create flattened objects with references replaced by {_id, _type}
        processedObjects.clear();
        queue.length = 0;
        queue.push(this.dict[graphUri]);

        // Process all objects in the objectMap to create flattened versions
        const CHUNK_SIZE = 500;
        let currentChunk = [];
        let processedCount = 0;

        // Process all objects in the objectMap
        for (const [id, obj] of objectMap.entries()) {
            // Create a flattened copy of the object
            const flattenedObj = { ...obj };

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

            // Add to current chunk
            currentChunk.push(flattenedObj);

            // When chunk is full, insert it into the collection
            if (currentChunk.length >= CHUNK_SIZE) {
                // first full test blew a gasket on some resource too large.
                // maybe that could happen if we didn't get out all the circ refs
                // this doesn't seem to happen, that's good
                if (false) {
                    // we need a check here to be sure that everything got flattened
                    // _.cloneDeepWith is an easy way to inspect the entire depth of an object.
                    // this customizer is used to confirm there are no unflattened instances of Fact or Rule
                    const checkNoFactOrRule = (value, key, object, stack) => {
                        // console.log("checkNoFactOrRule on key",key);
                        if (Fact.isFact(value) || Rule.isRule(value)) {
                            throw new Error(`Found unflattened Fact or Rule ${value._id}`);
                        }
                    };
                    // first full test blew a gasket on some resource too large.
                    // maybe that could happen if we didn't get out all the circ refs
                    // this doesn't seem to happen, that's good
                    try {
                        _.cloneDeepWith(currentChunk, checkNoFactOrRule);
                    }
                    catch (error) {
                        console.error(`error somewhere before ${processedCount + currentChunk.length}`, error);
                        throw error
                    }
                }

                const bulkOp = collection.initializeUnorderedBulkOp();
                for (const item of currentChunk) {
                    // Facts which are Causes can have very large _seen Sets.
                    // I tried saving them separately in chunks (below),
                    // but that seems to just run forever.
                    // Alternatively, I'm thinking that once the graph is fully reasoned,
                    // then it can be said that every Cause has seen every fact, so maybe
                    // they don't need to be saved, but when reasoner is restored,
                    // TODO figure out how best to restore _seen
                    delete item._seen;
                    if (false) {
                        const _seenLength = item._seen ? Object.keys(item._seen).length : 0;
                        if (_seenLength > 1000) {
                            // have to chunk em up.
                            console.log(`item ${item._id} has ${_seenLength} _seen`);
                            const _seen = Object.keys(item._seen);
                            item._seen = {};
                            // we have to chunk the _seen array, and insert each chunk,
                            // as an item with an _id thats `${item._id}_seen_${chunkIndex}`
                            // then insert the chunk _id into the item._seen object.

                            // Chunk the _seen array into smaller pieces
                            const CHUNK_SIZE = 500; // Smaller chunks for better performance
                            const numChunks = Math.ceil(_seen.length / CHUNK_SIZE);

                            // Create a new object to store chunk references
                            const chunkedSeen = {};

                            // Process each chunk
                            for (let i = 0; i < numChunks; i++) {
                                const start = i * CHUNK_SIZE;
                                const end = Math.min(start + CHUNK_SIZE, _seen.length);
                                const chunk = _seen.slice(start, end);

                                // Create a chunk object with a unique ID
                                const chunkId = `${item._id}_seen_${i}`;
                                const chunkObj = {
                                    _id: chunkId,
                                    _type: "SeenChunk",
                                    parentId: item._id,
                                    chunkIndex: i,
                                    totalChunks: numChunks,
                                    values: chunk
                                };
                                console.log(`inserting chunk ${chunkId} for ${item._id}`);
                                // Add the chunk to the current batch
                                bulkOp.insert(chunkObj);

                                // Store the reference to this chunk in the item's _seen object
                                chunkedSeen[chunkId] = true;
                            }

                            // Replace the original _seen with the chunked version
                            item._seen = chunkedSeen;
                        }
                    }

                    let error;
                    try {
                        bulkOp.insert(item);
                    }
                    catch (e) {
                        console.error(`error inserting ${item._id}`,e);
                        error = e;
                    }
                    if (error) {
                        try {
                            // if the insert fails, then this fails every time
                            fs.writeFileSync("/tmp/error_item", JSON.stringify(item,null,2));
                        }
                        catch (e) {
                            console.error(`error stringifying ${item}`,e);
                        }
                    }
                    if (error) {
                        // maybe calc size?
                        function roughSizeOfObject(object) {
                            let path = [];
                            const objectList = new Set();
                            const stack = [object];
                            let bytes = 0;
                            const visited = new Set();

                            while (stack.length) {
                                const value = stack.pop();

                                switch (typeof value) {
                                    case 'boolean':
                                        bytes += 4;
                                        break;
                                    case 'string':
                                        bytes += value.length * 2;
                                        break;
                                    case 'number':
                                        bytes += 8;
                                        break;
                                    case 'object':
                                        if (!objectList.has(value)) {
                                            objectList.add(value);
                                            for (const prop in value) {
                                                if (value.hasOwnProperty(prop)) {
                                                    stack.push(value[prop]);
                                                }
                                            }
                                        }
                                        else {
                                            console.error(`roughSizeOfObject found circular reference on prop ${prop}`);
                                        }
                                        break;
                                }
                            }

                            return bytes;
                        }
                        const size = roughSizeOfObject(item);
                        console.error("roughSizeOfObject", size/(1024*1024));
                    }

                }
                await bulkOp.execute();
                processedCount += currentChunk.length;
                console.log(`Processed ${processedCount} objects for graph ${graphUri}`);
                currentChunk = [];
            }
        }

        // Process any remaining items in the last chunk
        if (currentChunk.length > 0) {
            const bulkOp = collection.initializeUnorderedBulkOp();
            for (const item of currentChunk) {
                delete item._seen;
                bulkOp.insert(item);
            }
            await bulkOp.execute();
            processedCount += currentChunk.length;
            console.log(`Processed ${processedCount} objects for graph ${graphUri}`);
        }
    }

    // Finally, save the Dictionary itself (without dict and index)
    const _dict = Dictionary.clone(this);
    delete _dict.dict;
    delete _dict.index;
    delete _dict._seen;
    await collection.insertOne(_dict);

    return collection;
};

/**
 * @deprecated _This major effort appears to be a failure. The restored reasoner
 * doesn't find expected inferences. The use of a globally seen Fact Set appears
 * to be the problem._
 */
Dictionary.prototype.loadFromCollection = async function(collection, opts) {
    opts = opts || {};
    opts.reload = opts.reload !== false;
    opts.yieldMs = typeof opts.yieldMs === "number" ? opts.yieldMs : 50;
    console.log("loadFromCollection with yieldMs",opts.yieldMs);
    if (opts.reload) {
        // Find the Dictionary document
        const details = await collection.findOne({ _type: "Dictionary" });
        if (details) {
            Object.assign(this, details);
        }
        this.dict = {
            '#default': {}
        };
        this.index = {
            "#default": {
                predicate: {
                    subject: {
                        object: null
                    }
                }
            }
        };
    }

    // First pass: populate objectMap with all objects converted to instances
    const objectMap = new Map();
    const BATCH_SIZE = 1000;
    let processedCount = 0;
    let lastYieldTime = Date.now();

    // Use cursor to process documents in batches
    const cursor = collection.find({ _type: { $ne: "Dictionary" } });
    console.log(`Begin processing ${await cursor.count()} documents from collection.`);
    let batch = [];

    for await (const doc of cursor) {
        if (!doc) continue;

        let replacement;
        switch (doc._type) {
            case "Fact":
                if (!Fact.isFact(doc)) {
                    replacement = Fact.clone(doc);
                }
                break;
            case "Rule":
                if (!Rule.isRule(doc)) {
                    replacement = Rule.clone(doc);
                }
                break;
            case "Dictionary":
                if (!Dictionary.isDictionary(doc)) {
                    replacement = Dictionary.clone(doc);
                }
                break;
            default:
        }

        if (replacement) {
            objectMap.set(doc._id, replacement);
        } else {
            objectMap.set(doc._id, doc);
        }

        processedCount++;
        batch.push(doc);

        // Only yield if we've processed a full batch or enough time has passed
        const now = Date.now();
        if (batch.length >= BATCH_SIZE || now - lastYieldTime > 100) {
            await new Promise(resolve => setTimeout(resolve, opts.yieldMs)); // Yield to event loop
            batch = [];
            lastYieldTime = now;
        }

        // Log progress for large collections
        if (processedCount % (BATCH_SIZE * 10) === 0) {
            console.log(`Processed ${processedCount} documents into objectMap in first pass`);
        }
    }

    console.log(`First pass complete. Processed ${processedCount} documents into objectMap.`);
    console.log(`objectMap has ${objectMap.size} entries`);

    // Second pass: replace all {_id, _type} references with actual instances
    const queue = [];
    const processedObjects = new Set();
    let secondPassCount = 0;
    batch = [];
    lastYieldTime = Date.now();

    // Add all instances to the queue for processing using iterator
    const iterator = objectMap.values();
    let iteratorResult = iterator.next();

    while (!iteratorResult.done) {
        queue.push(iteratorResult.value);
        iteratorResult = iterator.next();
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
        secondPassCount++;
        batch.push(obj);

        // Only yield if we've processed a full batch or enough time has passed
        const now = Date.now();
        if (batch.length >= BATCH_SIZE || now - lastYieldTime > 100) {
            await new Promise(resolve => setTimeout(resolve, opts.yieldMs)); // Yield to event loop
            batch = [];
            lastYieldTime = now;
        }

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
        // Log progress for large collections
        if (secondPassCount % (BATCH_SIZE * 10) === 0) {
            console.log(`Processed ${secondPassCount} objects looking for Facts and Rules in second pass`);
        }
    }

    console.log(`Second pass complete. Processed ${secondPassCount} objects.`);

    // Third pass: add instances to the dictionary using this.put
    let thirdPassCount = 0;
    batch = [];
    lastYieldTime = Date.now();

    // Use iterator for the third pass as well
    const factIterator = objectMap.values();
    let factIteratorResult = factIterator.next();

    while (!factIteratorResult.done) {
        const instance = factIteratorResult.value;
        if (Fact.isFact(instance)) {
            if (!Fact.isCause(instance)) {
                for (const graphUri of instance.graphs || ["#default"]) {
                    this.put(instance, graphUri);
                    thirdPassCount++;
                    batch.push(instance);

                    // Only yield if we've processed a full batch or enough time has passed
                    const now = Date.now();
                    if (batch.length >= BATCH_SIZE || now - lastYieldTime > 100) {
                        await new Promise(resolve => setTimeout(resolve, opts.yieldMs)); // Yield to event loop
                        batch = [];
                        lastYieldTime = now;

                    }
                }
            }
            // Log progress for large collections
            if (thirdPassCount % (BATCH_SIZE * 10) === 0) {
                console.log(`Added ${thirdPassCount} Facts to dictionary`);
            }
        }

        factIteratorResult = factIterator.next();
    }
    console.log(`Third pass complete. Added ${thirdPassCount} Facts to dictionary.`);
    console.log("Now populate _seen");
    let _seenCt = 0;
    for (const graph in this.dict) {
        for (const ttl in this.dict[graph]) {
            const facts = this.dict[graph][ttl];
            for (const fact of facts) {
                _seenCt++;
                if (_seenCt % 1000 === 0) {
                    console.log(`Added ${_seenCt} Facts to seen.`);
                    await new Promise(resolve => setTimeout(resolve, opts.yieldMs));
                }
                this._seen.add(fact.asString);
            }
        }
    }
    console.log(`this._seen has ${this._seen.size} items`);

    return this;
};

module.exports = Dictionary;
