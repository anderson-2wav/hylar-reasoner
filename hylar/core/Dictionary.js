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

function Dictionary() {
    this.dict = {
        '#default': {}
    };
    this.lastUpdate = 0;
    this.purgeThreshold = 13000000;

    // index idea
    this.index = {
        predicate: {
            subject: {
                object: null
            }
        }
    }
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
 * @returns {*}
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
 * @param fact
 * @returns {*}
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

Dictionary.prototype.getIndex = function(s,p,o,graph) {
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

module.exports = Dictionary;
