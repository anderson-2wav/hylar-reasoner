/* eslint-disable */
/**
 * Created by Spadon on 11/09/2015.
 */

var h = require('../hylar');

var Logics = require('./Logics/Logics'),
    Solver = require('./Logics/Solver'),
    Utils = require('./Utils');

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
     * @param {Fact[]} F set of all known Facts
     * @param {Rule} R set of rules
     * @param {string[]} subjects to whitelist
     */
    incremental: function (FeAdd, FeDel, F, R, whitelist) {
        var Rdel = [], Rred = [], Rins = [],
            FiDel = [], FiAdd = [],
            FiDelNew = [], FiAddNew = [],
            superSet = [], insertionLoopCt = 0,

            additions, deletions,

            Fe = Logics.getOnlyExplicitFacts(F),
            Fi = Logics.getOnlyImplicitFacts(F),
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
                Solver.evaluateRuleSet(Rdel, Utils.uniques(Utils.uniques(Fi, Fe), FeDel), F)
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
                Solver.evaluateRuleSet(Rred, Utils.uniques(Fe, Fi), F)
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
                FiAdd = Utils.uniques(FiAdd, FiAddNew);
                const kb = Utils.uniques(F,FiAddNew);
                if (insertionLoopCt === 1) {
                    // the first time through, reason over all new E and I
                    superSet = Utils.uniques(FiAdd, FeAdd);
                }
                else {
                    // subsequent recursions, only reason over new I from last round
                    superSet = FiAddNew;
                }
                // another temporary hack
                Solver._verbose = true;
                console.log(`incremental insertionEvaluationLoop #${insertionLoopCt} over ${superSet.length} facts.`);
                if (FiAdd.length) {
                    // TODO experimental... why use the entire superset here?
                    // don't we only care about rules that might touch the inserted set?
                    // in practice this makes very little difference in outcome,
                    Rins = Logics.restrictRuleSet(R, FiAdd);
                }
                else {
                    Rins = Logics.restrictRuleSet(R, superSet);
                }

                // console.log(`incremental insertionEvaluationLoop evaluate restricted set ${Rins.length} of ${R.length} rules.`);
                Solver._phase = "insertion"; // temporary hack!
                Solver._round = insertionLoopCt;
                Solver.evaluateRuleSet(Rins, superSet, kb,undefined, undefined, whitelist)
                    .then(function(values) {
                        FiAddNew = values.cons;
                        if (!Utils.containsSubset(FiAdd, FiAddNew)) {
                            insertionEvaluationLoop();
                        } else {
                            // the current impl will recreate some I that are already known (in F). prune them
                            const newFiAdd = _.differenceBy(FiAdd, F, "asString");
                            additions = Utils.uniques(FeAdd, newFiAdd);
                            deletions = Utils.uniques(FeDel, FiDel);
                            deferred.resolve({
                                additions: additions,
                                deletions: deletions
                            });
                        }
                    }).fail(function(err) {
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
