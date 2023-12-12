/**
 * Created by pc on 27/01/2016.
 */
/* eslint-disable */
var Fact = require('./Fact');
var Logics = require('./Logics');
var Utils = require('../Utils');

var emitter = require('../Emitter');

var q = require('q');
var _ = require('lodash');


/**
 * Core solver used to evaluate rules against facts
 * using pattern matching mechanisms.
 */

Solver = {
    /**
     * Evaluates a set of rules over a set of facts.
     * @param {Rule[]} rs
     * @param {Fact[]} facts (new) to be evaluated
     * @param {Fact[]} [kb] all known facts
     * @returns Array of the evaluation.
     */
    evaluateRuleSet: function(rs, facts, kb,  doTagging, resolvedImplicitFactSet, whitelist) {
        this.kb = kb ?? [];
        this.graphHash = Utils.stringHash(this.kb.map(f => f.asString));
        var deferred = q.defer(), promises = [], cons = [], filteredFacts;
        for (var key in rs) {
            if (doTagging) {
                promises.push(this.evaluateThroughRestrictionWithTagging(rs[key], facts, resolvedImplicitFactSet));
            } else {
                // console.log(`evaluate rule #${key}: ${rs[key].name}`);
                promises.push(this.evaluateThroughRestriction(rs[key], facts, whitelist));
            }
        }
        try {
            q.all(promises).then(function (consTab) {
                for (var i = 0; i < consTab.length; i++) {
                    cons = cons.concat(consTab[i]);
                }
                deferred.resolve({cons: cons});
            });
        } catch(e) {
            deferred.reject(e);
        }
        return deferred.promise;
    },

    /**
     * Evaluates a rule over a set of facts through
     * restriction of the rule's causes.
     * @param {Rule} rule
     * @param {Fact[]} facts
     * @param {Fact[]} kb
     * @returns {Array}
     */
    evaluateThroughRestriction: function(rule, facts, whitelist) {
        // if (rule.name === "cax-sco") {
        //     debugger;
        // }
        if (Solver._verbose) {
            console.log(`Begin evaluate ${rule.name}`);
        }
        var consequences = [], deferred = q.defer();
        // find all the matching ?x variables in causes
        var mappingList = this.getMappings(rule, facts);
        try {
            this.checkOperators(rule, mappingList);

            for (var i = 0; i < mappingList.length; i++) {
                if (mappingList[i]) {
                    const mapping = mappingList[i];
                    // Replace mappings on all consequences
                    for (var j = 0; j < rule.consequences.length; j++) {
                        const consequence= this.substituteFactVariables(mapping, rule.consequences[j], [], rule);
                        // right here, keep from creating useless broken inferences like
                        //"XYZ" rdf:type xsd:string
                        if (consequence.subject?.[0] === '"') {
                            // console.log(`ignore consequence for subject: ${consequence.subject}`);
                            continue;
                        }
                        if (whitelist) {
                            if (whitelist.includes(consequence.subject)) {
                                consequences.push(consequence);
                            }
                        }
                        else {
                            // console.log(`${rule.name} add consequence for mapping ${i}`);
                            consequences.push(consequence);
                        }
                    }
                }
            }
            if (Solver._verbose) {
                console.log(`return ${consequences.length} consequences for rule ${rule.name}`);
            }
            deferred.resolve(consequences);
        } catch(e) {
            deferred.reject(e);
        }

        return deferred.promise;
    },

    /**
     * Evaluates a rule over a set of facts through
     * restriction of the rule's causes with tagging.
     * @param rule
     * @param kb
     * @returns {Array}
     */
    evaluateThroughRestrictionWithTagging: function(rule, kb) {
        var mappingList = this.getMappings(rule, kb), deferred = q.defer(),
            consequences = [], consequence, causes, iterationConsequences;

        this.checkOperators(rule, mappingList);

        try {
            for (var i = 0; i < mappingList.length; i++) {
                if (mappingList[i]) {
                    // Replace mappings on all consequences
                    causes = Logics.buildCauses(mappingList[i].__facts__);
                    iterationConsequences = [];
                    for (var j = 0; j < rule.consequences.length; j++) {
                        consequence = this.substituteFactVariables(mappingList[i], rule.consequences[j], causes, rule)
                        consequences.push(consequence)
                        iterationConsequences.push(consequence)
                    }
                    try {
                        Logics.addConsequences(mappingList[i].__facts__, iterationConsequences);
                    } catch(e) {
                        throw "Error when trying to add consequences on the implicit fact.";
                    }
                }
            }
            deferred.resolve(consequences);
        } catch(e) {
            deferred.reject(e);
        }

        return deferred.promise;
    },

    checkOperators: function(rule, mappingList) {
        var causes = rule.operatorCauses,
            operationToEvaluate, substitutedFact;

        if (rule.operatorCauses.length == 0) return mappingList;

        for (var i = 0; i < mappingList.length; i++) {
            for (var j = 0; j < causes.length; j++) {
                substitutedFact = this.substituteFactVariables(mappingList[i], causes[j]);
                try {
                    operationToEvaluate = Utils.getValueFromDatatype(substitutedFact.subject) +
                        substitutedFact.predicate +
                        Utils.getValueFromDatatype(substitutedFact.object);
                } catch(e) {
                    throw e;
                }
                if (!eval(operationToEvaluate)) {
                    delete mappingList[i];
                    break;
                }
            }
        }

    },

    getMappings: function(rule, facts, consequences) {
        var i = 0, mappingList, causes;

        var currentCauses = [rule.causes[i]]; // Init with first cause

        while (i < rule.causes.length) {
            mappingList = this.substituteNextCauses(currentCauses, rule.causes[i+1], facts, rule.constants, rule);

            // each cause in currentCauses may have a _nextCauses
            const nextCauses = [];
            for (const c of currentCauses) {
                if (c._nextCauses) {
                    nextCauses.push(...c._nextCauses);
                }
            }
            currentCauses = nextCauses;
            i++;
        }
        return mappingList;
    },

    /**
     * Updates the mapping of the current cause
     * given the next cause of a rule, over a
     * set of facts.
     * @param {Fact[]} currentCauses
     * @param {Fact} [nextCause]
     * @param {Fact[]} facts new Facts to be evaluated
     * @returns {Mapping[]} after last cause, returns complete mappings list
     */
    substituteNextCauses: function(currentCauses, nextCause, facts, constants, rule) {
        var mappings = [];

        for (var i = 0; i < currentCauses.length; i++) {
            var currentCause = currentCauses[i];
            const ckey = currentCause.toString();
            if (Solver._verbose && j>0 && j % 10000 === 0) {
                console.log(`Rule ${rule.name} cause ${ckey} eval ${j} of ${facts.length} facts.`);
            }
            if (this.graphHash !== currentCause.graphHash) {
                if (Solver._verbose) {
                    console.log(`cause ${ckey} has not seen some facts. Evaluate all.`);
                    // if (currentCause._seen) {
                    //     console.log(`cause ${ckey} has _seen`,Object.keys(currentCause._seen));
                    // }
                    // else {
                    //     console.log(`${ckey} never _seen.`);
                    // }
                }
                facts = Utils.uniques(this.kb, facts);
            }
            currentCause._seen = currentCause._seen ?? {};
            currentCause._nextCauses = currentCause._nextCauses ?? [];
            let evalCt = 0;
            let skippedCt = 0;
            for (var j = 0; j < facts.length; j++) {
                const fact = facts[j];
                var fkey = fact.toString();
                if (currentCause._seen[fkey]) {
                    // console.log(`rule ${rule.name} cause ${ckey} skip OLD ${fkey}`);
                    skippedCt++;
                    continue;
                }
                // console.log(`rule ${rule.name} cause ${ckey} NEW ${fkey}`);
                evalCt++;
                currentCause._seen[fkey] = 1;

                if (Solver._verbose && j>0 && j % 10000 === 0) {
                    console.log(`Rule ${rule.name} cause ${ckey} eval ${j} of ${facts.length} facts.`);
                }
                // Get the mapping of the current cause ...
                var mapping = currentCause.mapping,
                    substitutedNextCause,
                    newMapping;
                // ... or build a fresh one if it does not exist
                if (mapping === undefined) {
                    mapping = {};
                    mapping.__facts__ = [];
                }

                // Update the mapping using pattern matching
                newMapping = this.factMatches(fact, currentCause, mapping, constants, rule);

                // If the current fact matches the current cause ...
                if (newMapping) {
                    // If there are other causes to be checked...
                    if (nextCause) {
                        // Substitute the next cause's variable with the new mapping
                        substitutedNextCause = this.substituteFactVariables(newMapping, nextCause, [], rule);
                        substitutedNextCause.mapping = newMapping;
                        substitutedNextCause._fromCause = currentCause;
                        currentCause._nextCauses.push(substitutedNextCause);
                    } else {
                        // Otherwise, add the new mapping to the returned mapping array
                        mappings.push(newMapping);
                    }
                }
            }
            // this cause has seen some new facts...
            if (evalCt) {
                const strs = Object.keys(currentCause._seen);
                currentCause.graphHash = Utils.stringHash(strs);
            }
        }
        return mappings;
    },

    /**
     * Returns a new or updated mapping if a fact matches a rule cause or consequence,
     * return false otherwise.
     * @param fact
     * @param ruleFact
     * @param mapping
     * @returns {*}
     */
    factMatches: function(fact, ruleFact, mapping, constants, rule) {
        var localMapping = {};

        // Checks and update localMapping if matches
        if (!this.factElemMatches(fact.predicate, ruleFact.predicate, mapping, localMapping)) {
            return false;
        }
        if (!this.factElemMatches(fact.object, ruleFact.object, mapping, localMapping)) {
            return false;
        }
        if (!this.factElemMatches(fact.subject, ruleFact.subject, mapping, localMapping)) {
            return false;
        }

        emitter.emit('rule-fired', rule.name);

        // If an already existing uri has been mapped...
        /*for (var key in localMapping) {
            if(constants.indexOf(localMapping[key]) !== -1) {
                return false;
            }
        }*/

        // Merges local and global mapping
        for (var mapKey in mapping) {
            if (mapKey == '__facts__') {
                localMapping[mapKey] = Utils.uniques(mapping[mapKey], [fact]);
            } else {
                for (key in localMapping) {
                    if (mapping[mapKey] == localMapping[key]) {
                        if (mapKey != key) {
                            return false;
                        }
                    }
                }
                localMapping[mapKey] = mapping[mapKey];
            }
        }

        // The new mapping is updated
        return localMapping;
    },

    factElemMatches: function(factElem, causeElem, globalMapping, localMapping) {
        if (causeElem.indexOf('?') === 0) {
            if (globalMapping[causeElem] && (globalMapping[causeElem] != factElem)) {
                return false;
            } else {
                localMapping[causeElem] = factElem;
            }
        } else {
            if (factElem != causeElem) {
                return false;
            }
        }

        return true;
    },

    /**
     * Substitutes an element given the mapping.
     * @param elem
     * @param mapping
     * @returns {*}
     */
    substituteElementVariablesWithMapping: function(elem, mapping) {
        if(Logics.isBNode(elem)) {
            return Logics.skolemize(mapping.__facts__, elem);
        } else if(Logics.isVariable(elem)) {
            if (mapping[elem] !== undefined) {
                return mapping[elem]
            }
        }
        return elem;
    },

    /**
     * Substitutes fact's variable members (sub, pred, obj)
     * given the mapping.
     * @param mapping
     * @param notYetSubstitutedFact
     * @param causedBy
     * @param rule
     * @returns {Fact}
     */
    substituteFactVariables: function(mapping, notYetSubstitutedFact, causedBy, rule) {
        var subject, predicate, object, substitutedFact;
        if (mapping == {}) { // does this work? :-/
            return notYetSubstitutedFact;
        }
        subject = this.substituteElementVariablesWithMapping(notYetSubstitutedFact.subject, mapping);
        predicate = this.substituteElementVariablesWithMapping(notYetSubstitutedFact.predicate, mapping);
        object = this.substituteElementVariablesWithMapping(notYetSubstitutedFact.object, mapping);

        substitutedFact = new Fact(predicate, subject, object, [], false);

        if (causedBy) {
            substitutedFact.causedBy = causedBy;
            substitutedFact.explicit = false;
        }

        if (rule) {
            substitutedFact.rule = rule;
            substitutedFact.mapping = mapping;
        }

        return substitutedFact;
    },

    causesAreIndependent: function(cause1, cause2) {
        const cause1Vars = [];
        const cause2Vars = [];
        [cause1,cause2].forEach((cause,i) => {
            const vars = [cause1Vars,cause2Vars][i];
            ["subject","predicate","object"].forEach((k) => {
                if (cause[k].indexOf("?") === 0) {
                    vars.push(cause[k]);
                }
            });
        });
        return _.intersection(cause1Vars,cause2Vars).length === 0;
    }
};

module.exports = Solver;
