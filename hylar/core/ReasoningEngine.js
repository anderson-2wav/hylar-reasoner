/* eslint-disable */
/**
 * Created by Spadon on 11/09/2015.
 */

var h = require('../hylar');

var Logics = require('./Logics/Logics'),
    Solver = require('./Logics/Solver'),
    Utils = require('./Utils');
    Dictionary = require('./Dictionary');

var q = require('q');
var _ = require('lodash');
/**
 * Reasoning engine containing incremental algorithms
 * and heuristics for KB view maintaining.
 */

ReasoningEngine = {
    /**
     * A naive reasoner that recalculates the entire knowledge base.
     * @deprecated
     * @param triplesIns
     * @param triplesDel
     * @param rules
     * @returns {{fi: *, fe: *}}
     */
    naive: function(FeAdd, FeDel, F, R) {
        var FiAdd = [], FiAddNew = [], additions, deletions,
            Fe = Logics.getOnlyExplicitFacts(F), FiAddNew = [];

        // Deletion
        if(FeDel && FeDel.length) {
            Fe = Logics.minus(Fe, FeDel);
        }

        // Insertion
        if(FeAdd && FeAdd.length) {
            Fe = Utils.uniques(Fe, FeAdd);
        }

        // Recalculation
        do {
            FiAdd = Utils.uniques(FiAdd, FiAddNew);
            FiAddNew = Solver.evaluateRuleSet(R, Utils.uniques(Fe, FiAdd), F);
        } while (!Logics.containsFacts(FiAdd, FiAddNew));

        additions = Utils.uniques(FeAdd, FiAdd);
        deletions = Logics.minus(F, Utils.uniques(Fe, FiAdd));

        F = Utils.uniques(Fe, FiAdd);

        return {
            additions: additions,
            deletions: deletions,
            updatedF: F
        };
    },

    /**
     * Incremental reasoning which avoids complete recalculation of facts.
     * Concat is preferred over merge for evaluation purposes.
     * @param {Fact[]} FeAdd all explicit added
     * @param {Fact[]} FeDel all explicit deleted
     * @param {Dictionary} D dict of all known Facts
     * @param {Rule} R set of rules
     * @param {string[]} subjects to whitelist
     */
    incremental: function (FeAdd, FeDel, D, R, whitelist) {
        var Rdel = [], Rred = [], Rins = [],
            FiDel = [], FiAdd = [],
            FiDelNew = [], FiAddNew = [],
            superSet = [], insertionLoopCt = 0,

            additions, deletions,

          // KB is the flattened dictionary. Updated at iterations.
          // (I'm concerned about efficiency of this operation)
            KB = D.values(),
          // D is a clone of the dictionary that can be added/removed
          // without affecting the original (from Hylar).
          // Represents the entire set of known facts,
          // including facts added/removed during iteration.
            D = D.clone(),

          // did this ever work? getOnlyExplicitFacts expects a dict,
          // but it was previously being passed a [], afaict.
            Fe = Logics.getOnlyExplicitFacts(KB),
            Fi = Logics.getOnlyImplicitFacts(KB),
            // where F is all facts known before
            // FeAdd is all new explicit added
            // FeDel is all new


        deferred = q.defer(),

            startAlgorithm = function() {
                console.log("incremental startAlgorithm");
                overDeletionEvaluationLoop();
            },

            overDeletionEvaluationLoop = function() {
                //console.log("incremental overDeletionEvaluationLoop");
                FiDel = Utils.uniques(FiDel, FiDelNew);
                Rdel = Logics.restrictRuleSet(R, Utils.uniques(FeDel, FiDel));
                Solver._phase = "deletion"; // temporary hack!
                Solver.evaluateRuleSet(Rdel, Utils.uniques(Utils.uniques(Fi, Fe), FeDel), KB, D)
                    .then(function(values) {
                        FiDelNew = values.cons;
                        if (Utils.uniques(FiDel, FiDelNew).length > FiDel.length) {
                            overDeletionEvaluationLoop();
                        } else {
                            Fe = Logics.minus(Fe, FeDel);
                            Fi = Logics.minus(Fi, FiDel);
                            rederivationEvaluationLoop();
                        }
                    });
            },

            rederivationEvaluationLoop = function() {
                //console.log("incremental rederivationEvaluationLoop");
                FiAdd = Utils.uniques(FiAdd, FiAddNew);
                Rred = Logics.restrictRuleSet(R, FiDel);
                Solver._phase = "rederivation"; // temporary hack!
                Solver.evaluateRuleSet(Rred, Utils.uniques(Fe, Fi), KB, D)
                    .then(function(values) {
                        FiAddNew = values.cons;
                        if (Utils.uniques(FiAdd, FiAddNew).length > FiAdd.length) {
                            rederivationEvaluationLoop();
                        } else {
                            insertionEvaluationLoop();
                        }
                    });
            },

            insertionEvaluationLoop = function() {
                insertionLoopCt++;
                // subsequent recursions, only reason over new I from last round
                let insertionSet = FiAddNew ?? [];
                // the first time through, reason over added explicit.
                if (insertionLoopCt === 1) {
                    // FiAdd is probably empty.
                    insertionSet = Utils.uniques(FiAdd, FeAdd);
                }

                Solver._verbose = false;
                console.log(`incremental insertionEvaluationLoop #${insertionLoopCt} inserting ${insertionSet.length} facts.`);
                Rins = Logics.restrictRuleSet(R, insertionSet);
                // if (FiAdd.length) {
                //     // not worth the bother...
                //     // TODO experimental... why use the entire superset here?
                //     // don't we only care about rules that might touch the inserted set?
                //     // in practice this makes very little difference in outcome,
                //     Rins = Logics.restrictRuleSet(R, FiAdd);
                // }

                // console.log(`incremental insertionEvaluationLoop evaluate restricted set ${Rins.length} of ${R.length} rules.`);
                Solver._phase = "insertion"; // temporary hack!
                Solver._round = insertionLoopCt;
                Solver.evaluateRuleSet(Rins, insertionSet, KB, D,undefined, undefined, whitelist)
                    .then(function(values) {
                        FiAddNew = values.cons;
                        // problem: reasoning my assert new I's
                        // that are already known to the KB, from before
                        FiAddNew = _.differenceBy(FiAddNew,KB,"asString");
                        if (!Utils.containsSubset(FiAdd, FiAddNew)) {
                            // remember the new I in the total set, without duplicates
                            FiAdd = Utils.uniques(FiAdd, FiAddNew);
                            if (insertionLoopCt === 1) {
                                // explicit facts that were added
                                // need to be added to D _once_
                                for (let i=0; i < FeAdd.length; i++) {
                                    D.put(FeAdd[i]);
                                }
                                // // need to be added to the KB _once_
                                // KB.push(...FeAdd);
                            }
                            // add new statements to the known D,
                            // for next iteration
                            // need to be added to D _once_
                            for (let i=0; i < FiAddNew.length; i++) {
                                D.put(FiAddNew[i]);
                            }
                            // KB.push(...FiAddNew); // concat may be faster, but use more memory. would be interesting test.
                            // KB is needed for _.differenceBy, so update it now
                            KB = D.values();
                            console.log(`insertionEvaluationLoop #${insertionLoopCt} inferred ${FiAddNew.length} facts.`);
                            insertionEvaluationLoop();
                        } else {
                            // remember the new I in the total set, without duplicates
                            FiAdd = Utils.uniques(FiAdd, FiAddNew);
                            console.log(`incremental reasoner returning E ${FeAdd.length} and I ${FiAdd.length} facts.`);
                            additions = Utils.uniques(FeAdd, FiAdd);
                            deletions = Utils.uniques(FeDel, FiDel);
                            deferred.resolve({
                                additions: additions,
                                deletions: deletions
                            });
                        }
                    }).fail(function(err) {
                        console.error("incremental insert error:",err);
                        h.displayError(err);
                    });
            };

        startAlgorithm();
        return deferred.promise;
    },

    /**
     * Returns valid facts using explicit facts' validity tags.
     * @param F
     * @param refs
     * @returns {Array}
     */
    tagFilter: function(F) {
        var validSet = [];
        for (var i = 0; i < F.length; i++) {
            if (F[i].isValid()) {
                validSet.push(F[i]);
            }
        }
        return validSet;
    },

    /**
     * Tags newly inferred facts, and (un)validates updated ones.
     * Explicit facts are 'validity'-tagged, while
     * implicit ones are 'causedBy'-tagged.
     * @param FeAdd
     * @param FeDel
     * @param F
     * @param R
     * @returns {{additions: *, deletions: Array}}
     */
    tagging: function(FeAdd, FeDel, F, R) {
        var newExplicitFacts, resolvedExplicitFacts, validUpdateResults,
            FiAdd = [], Rins = [], deferred = q.defer(),
            Fi = Logics.getOnlyImplicitFacts(F), Fe,

            startAlgorithm = function() {
                if(newExplicitFacts.length > 0) {
                    evaluationLoop(F);
                } else {
                    deferred.resolve({
                        additions: resolvedExplicitFacts,
                        deletions: []
                    });
                }
            },

            evaluationLoop = function() {
                F = Utils.uniques(F, Fi);
                Rins = Logics.restrictRuleSet(R, F);
                Solver.evaluateRuleSet(Rins, F, undefined, true)
                    .then(function(values) {
                        FiAdd = values.cons;
                        if (Logics.unify(FiAdd, Fi)) {
                            setTimeout(evaluationLoop, 1);
                        } else {
                            deferred.resolve({
                                additions: newExplicitFacts.concat(resolvedExplicitFacts, Fi),
                                deletions: []
                            });
                        }
                    });
            };

        // Returns new explicit facts to be added
        validUpdateResults = Logics.updateValidTags(F, FeAdd, FeDel);
        newExplicitFacts = validUpdateResults.new;
        resolvedExplicitFacts = validUpdateResults.resolved;
        F = F.concat(newExplicitFacts);
        startAlgorithm();

        return deferred.promise;
    }
};

module.exports = {
    incrementalBf: ReasoningEngine.incrementalBf,
    incremental: ReasoningEngine.incremental,
    tagging: ReasoningEngine.tagging,
    tagFilter: ReasoningEngine.tagFilter
};
