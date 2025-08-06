/* eslint-disable */
/**
 * Created by MT on 01/12/2015.
 */

const fs = require('fs'),
    chalk = require('chalk'),
    chalkRainbow = require('chalk-rainbow'),
    q = require('q'),
    util = require('util'),
    _ = require("lodash");

const Promise = require('bluebird');

const emitter = require('./core/Emitter');

const Dictionary = require('./core/Dictionary'),
    ParsingInterface = require('./core/ParsingInterface'),
    TripleStorageManager = require('./core/TripleStorageManager'),
    Logics = require('./core/Logics/Logics'),
    Reasoner = require('./core/Reasoner'),
    Rules = require('./core/Rules'),
    Utils = require('./core/Utils'),
    Errors = require('./core/Errors'),
    RegularExpressions = require('./core/RegularExpressions'),
    Prefixes = require('./core/Prefixes'),
    Axioms = require('./core/Axioms')

const logFile = 'hylar.log';

function debug() {
    if (process.env["HYLAR_DEBUG"]) {
        console.log.apply(undefined,arguments);
    }
}

/**
 * HyLAR main module.
 * @author Mehdi Terdjimi
 * @organization LIRIS, Universite Lyon 1
 * @email mehdi.terdjimi@univ-lyon1.fr
 * @param {object} [params]
 * @param {boolean} [params.reasoning=true]
 * @param {string} [params.dbDir="./db"]
 * @param {string} [params.entailment="owl2rl"] "rdfs" is also supported
 * @param {boolean} [params.persistent=false]
 */

class Hylar {
    constructor(params = {}) {
        this.dict = new Dictionary()
        this._customRules = []
        this.sm = new TripleStorageManager()
        this.sm.init()

        this.prefixes = Prefixes
        this.reasoning = params.reasoning !== false;
        this.dbDir = params.dbDir || './db';

        this._setEntailment(params.entailment)
        this._setupPersistence(params.persistent)

        this.queryHistory = []
        this.log = []
        this.parsingInterface = ParsingInterface;
        Hylar.currentInstance = this;
    }

    static log(msg) {
        let dateMsg = `[ ${new Date().toString()} ] ${msg}\n`
        Hylar.currentInstance.log.push(msg)
        fs.appendFileSync(logFile, dateMsg);
    }

    /**
     * Rule set getter.
     * Depends on the specified entailment
     * @return {*}
     */
    get rules() {
        return this._customRules.concat(Rules[this.entailment])
    }

    /**
     * Entailment-related axioms
     */
    get axioms() {
        return Axioms.getAxioms(this.entailment)
    }

    get reasoningMethod() {
        switch(this.rMethod) {
            case Reasoner.process.it.incrementally:
                return 'incremental'
                break
            case Reasoner.process.it.tagBased:
                return 'tagBased'
                break
            default:
                return 'none'
        }
    }

    /**
     * Sets up specified entailement,
     * then put axioms and compute rule dependencies
     * to optimize reasoning task time performance
     * @param entailment
     * @return {Promise<void>}
     * @private
     */
    async _setEntailment(entailment) {
        this.entailment = entailment != null ? entailment : 'owl2rl'
        Hylar.notify("Ignoring rule dependencies. I don't think they are used.");
        // Reasoner.updateRuleDependencies(this.rules);
    }

    /**
     * Process persistence task if specified
     * @param persistent
     * @private
     */
    async _setupPersistence(persistent) {
        if (persistent === true) {
            this.allowPersist = true
            this.restore()
        } else {
            this.allowPersist = false
        }
    }

    lastLog() {
        return this.log.length > 0 ? this.log[this.log.length-1] : ''
    }

    /**
     * Custom error display
     * @returns {*}
     */
    static displayError(error) {
        let msg = error.stack || error.toString()
        console.log(`${chalk.red('[HyLAR] ')} 😰 ${chalk.bold('ERROR:')} ${msg}`);
        try {
            Hylar.log(msg)
        } catch (e) {
            return Errors.FileIO(logFile);
        }
    }

    /**
     * Custom warning display
     * @returns {*}
     */
    static displayWarning(msg) {
        console.log(`${chalk.yellow('[HyLAR] ')} 😐 WARNING: ${msg}`);
        try {
            Hylar.log(msg)
        } catch (e) {
            return Errors.FileIO(logFile);
        }
    }

    /**
     * Notifications of HyLAR (similar to console.log behavior)
     * @returns {*}
     */
    static notify(msg, params = { silent: false }) {
        if (params.silent == false) console.log(chalk.green('[HyLAR] ') + msg);
        try {
            Hylar.log(msg)
        } catch (e) {
            return Errors.FileIO(logFile);
        }
    }

    static success(msg) {
        console.log(`${chalkRainbow('[HyLAR] ')} ✨ ${msg}`);
        try {
            Hylar.log(msg)
        } catch (e) {
            return Errors.FileIO(logFile);
        }
    }

    async setReasoningOn() {
        this.reasoning = true
        await this.recomputeClosure()
    }

    async setReasoningOff() {
        Hylar.displayWarning('Reasoning has been set off.')
        this.reasoning = false
        await this.recomputeClosure()
    }

    clean() {
        this.dict = new Dictionary();
        this.sm = new TripleStorageManager();
        this.sm.init();
        // TODO Facts have _seen to when they are Causes
        // rules may contain cached reasoning
        this.rules.forEach((r) => {
            (r.causes || []).forEach((c) => {
                delete c.graphHash;
                delete c._seen;
                delete c._nextCauses;
            });
        });
        this.persist();
    }

    /**
     * Puts on incremental reasoning
     */
    async setIncremental() {
        this.rMethod = Reasoner.process.it.incrementally;
        this.dict.turnOffForgetting();
        Hylar.notify('Reasoner set as incremental.');
    }

    /**
     * Puts on tag-based reasoning
     */
    async setTagBased() {
        this.rMethod = Reasoner.process.it.tagBased;
        this.dict.turnOnForgetting();
        Hylar.notify('Reasoner set as tag-based.');
    }

    async setRules(rules) {
        this.rules = rules;
        await this.recomputeClosure()
    }

    /**
     * Switches HyLAR's reasoning method
     * @param method Name of the method ('incremental' or 'tagBased')
     */
    updateReasoningMethod(method = 'incremental') {
        if (!this.rMethod) {
            switch (method) {
                case 'tagBased':
                    if (this.rMethod != Reasoner.process.it.tagBased) this.setTagBased()
                    break;
                case 'incremental':
                    if (this.rMethod != Reasoner.process.it.incrementally) this.setIncremental()
                    break;
                default:
                    Hylar.displayWarning(`Reasoning method ${method} not supported, using incremental instead.`)
                    this.setIncremental()
            }
        }
    }

    /**
     * Intializes the triple store, loads/classifies an ontology and register its
     * entities into the Dictionary.
     * @param ontologyTxt The raw ontology text
     * @param mimeType The specified mime type
     * @param reasoningMethod The desired reasoning method for the classification
     * @param graph (optional) The graph in which the ontology will be loaded
     * @param keepOldValues (optional - default: false) Avoid storage cleaning if set to true.
     * @returns {*}
     */
    async load(ontologyTxt, mimeType, keepOldValues, graph) {
        emitter.emit('classif-started');

        if (!keepOldValues) {
            this.dict.clear();
            await this.sm.init()
            return this.treatLoad(ontologyTxt, mimeType, graph)
        } else {
            return this.treatLoad(ontologyTxt, mimeType, graph)
        }
    }

    async treatLoad(ontologyTxt, mimeType, graph) {
        switch(mimeType) {
            case 'application/xml':
            case 'application/rdf+xml':
            case false:
                Hylar.error(`Unrecognized or unsupported mimeType. Supported formats are json-ld, turtle, n3`)
                return false;
                break;
            default:
                try {
                    // put in line breaks for easier parse debugging:
                    if (mimeType === "text/turtle") {
                        ontologyTxt = ontologyTxt.replace(/ \. /g," . \n");
                        // rdfstore N3 parser freaks out at backslash,
                        ontologyTxt = ontologyTxt.replace(/\\/g,"/");
                    }
                    var tmpFile = "/tmp/ontologyTxt"+Date.now();
                    console.log(`loading ontologyTxt.length=${ontologyTxt.length} writing to ${tmpFile}`);
                    fs.writeFileSync(tmpFile,ontologyTxt);
                    let rCt = await this.sm.load(ontologyTxt, mimeType)
                    console.log(`${rCt} triples loaded in the store`);

                    Hylar.notify(rCt + ' triples loaded in the store.', {  })
                    if (this.reasoning == true) {
                        return this.classify(graph)
                    } else {
                        // I've learned that explicit triples don't get loaded into graph
                        // when reasoning is off, or maybe never?
                        let r = await this.sm.query('CONSTRUCT { ?a ?b ?c } WHERE { ?a ?b ?c }')
                        for (let i = 0; i <  r.triples.length; i++) {
                            let triple = r.triples[i];
                            let _fs = this.dict.get(triple);
                            if(!_fs) {
                                let f = ParsingInterface.tripleToFact(triple, true, (this.rMethod == Reasoner.process.it.incrementally))
                                this.dict.put(f, graph)
                            }
                        }
                        return rCt;
                    }
                } catch (error) {
                  //console.log("HYLAR ERROR", error);
                    Hylar.displayError(error)
                    throw error;
                }
        }
    }

    /**
     * Launches a SPARQL query against the triplestore.
     * @param query The SPARQL query text
     * @param reasoningMethod The desired reasoning method if inserting/deleting
     * @param [syncCB] callback function
     * @param [persistDerivations] whether or not we're going to persist
     * @param {string[]} [whitelist] subject uris
     */
    async query(query, reasoningMethod, syncCB, persistDerivations, whitelist) {
        syncCB = syncCB || function(result) {};
        // Default persistDerivations to true like it would normally behave
        if (typeof persistDerivations === "undefined") {
          persistDerivations = true;
        }
        Hylar.notify("Begin query with persist: " + persistDerivations);

        let sparql, singleWhereQueries = [], result
        Hylar.notify(`Received ${query}`, { silent: true })

        try {
            // Parse original query
            sparql = ParsingInterface.parseSPARQL(query)
            console.log("sparql", sparql);
        } catch (e) {
            Hylar.displayError('Problem with SPARQL query: ' + query + "Error: " + e.message);
            throw e;
        }

        // TODO I THINK THIS IS THE WRONG WAY TO HANDLE UPDATES W/O REASONING
        // this updates the store, but never updates the dictionary,
        // so future reasoning will never see these inserts.
        if (false && this.reasoning == false) {
            return this.sm.query(query);
        }

        this.updateReasoningMethod(reasoningMethod);

        switch (sparql.type) {
            // Insert, delete queries
            case 'update':
                if (ParsingInterface.isUpdateWhere(sparql)) {
                    // a weird scoping error happens here..
                    // the sparql object gets changed by the inner query,
                    // even though it should not fwict.
                    const originalSparql = _.cloneDeep(sparql);
                    // Get construct results of the update where query
                    let sparqlConstruct = ParsingInterface.updateWhereToConstructWhere(sparql);
                    const sparqlStr = ParsingInterface.deserializeQuery(sparqlConstruct);
                    let data = await this.query(sparqlStr);
                    const parsingInt = ParsingInterface.buildUpdateQueryWithConstructResults(originalSparql, data);
                    // Put them back in a simple update data manner to provide inner-graph inference
                    return this.query(parsingInt, reasoningMethod, syncCB, persistDerivations);
                } else {
                    return this.treatUpdateWithGraph(query, syncCB, persistDerivations, whitelist);
                }
                break;

            // Select, Ask, Construct queries
            default:
                // If incremental query
                if (this.rMethod == Reasoner.process.it.incrementally) {
                    // To overcome rdfstore not supporting count; only supports count(*) though
                    let countStatements = []

                    if (sparql.hasOwnProperty('variables')) {
                        sparql.variables.forEach((_var, index) => {
                            if (_var.hasOwnProperty('expression') && _var.expression.aggregation == 'count') {
                                // If this is a count statement on a wildcard select, process it
                                if (_var.expression.expression == '*') {
                                    countStatements.push(_var)
                                    sparql.variables[index] = _var.expression.expression
                                    // Otherwise throw unsupported
                                } else {
                                    throw Errors.CountNotImplemented(_var.expression.expression)
                                }
                            }
                        })
                    }

                    // Execute query against the store
                    let results = []
                    try {
                        results = await this.sm.query(query)
                    } catch(err) {
                        throw err
                    }

                    // Reattach counted if relevant
                    if (countStatements.length > 0) {
                        countStatements.forEach(cntStm => {
                            if (cntStm.expression.expression == '*') {
                                // The count result that will be attached
                                let countResult = {
                                    token: 'literal',
                                    type: 'http://www.w3.org/2001/XMLSchema#integer',
                                    value: results.length
                                }

                                // Replace bindings
                                results.forEach((binding, index) => {
                                    Object.keys(binding).forEach(_var => {
                                        if (sparql.variables.indexOf(_var) == -1) {
                                            delete binding[_var]
                                        }
                                    })
                                    if (Object.keys(binding).length == 0) {
                                        delete results[index]
                                    }
                                })
                                results = results.filter(binding => binding)

                                // Either attach to remaining bindings or add a unique count binding
                                if (results.length > 0) {
                                    results.forEach(binding => {
                                        binding[cntStm.variable] = countResult
                                    })
                                } else {
                                    let binding = {}
                                    binding[cntStm.variable] = countResult
                                    results.push(binding)
                                }
                            } else {
                                throw Errors.CountNotImplemented(cntStm.expression.expression)
                            }
                        })
                    }

                    return results

                    // If tag-based query
                } else {
                    await this.sm.regenerateSideStore()

                    for (var i = 0; i < sparql.where.length; i++) {
                        singleWhereQueries.push(ParsingInterface.isolateWhereQuery(sparql, i))
                    }

                    await Promise.reduce(singleWhereQueries, (previous, singleWhereQuery) => {
                        return this.treatSelectOrConstruct(singleWhereQuery);
                    }, 0)

                    let results = await this.sm.querySideStore(query);

                    return results
                }
        }
    }

    /**
     * High-level treatUpdate that takes graphs into account.
     * @returns Promise
     */
    async treatUpdateWithGraph(query, syncCB, persistDerivations, whitelist) {
        syncCB = syncCB || function(result) {};
        if (typeof persistDerivations === "undefined") persistDerivations = true;

        var sparql = ParsingInterface.parseSPARQL(query),
            promises = [], updates;

        for (var i = 0; i < sparql.updates.length; i++) {
            if (sparql.updates[i].updateType == 'insert') {
                updates = sparql.updates[i].insert;
            } else if (sparql.updates[i].updateType == 'delete') {
                updates = sparql.updates[i].delete;
            }
            for (var j = 0; j < updates.length; j++) {
                promises.push(this.treatUpdate(updates[j], sparql.updates[i].updateType, syncCB, persistDerivations, whitelist));
            }
        }

        let values = await Promise.all(promises)
        return [].concat.apply([], values);

    }

    /**
     * Returns the content of the triplestore as turtle.
     * @returns {String}
     */
    async getStorage() {
        let content = await this.sm.getContent()
        return content.triples.toString();
    }

    /**
     * Empties and recreate the triplestore with elements
     * indicated in turtle/n3.
     * @param ttl The turtle/n3 triples to be added.
     * @returns {*}
     */
    setStorage(ttl) {
        return this.sm.createStoreWith(ttl);
    }

    getRulesAsStringArray() {
        var strRules = [];
        for (var i = 0; i < this.rules.length; i++) {
            strRules.push({ name: this.rules[i].name, rule: this.rules[i].toString(), type: this.rules[i].type } );
        }
        return strRules;
    }

    /**
     * Returns the dictionary content.
     * @returns {Object}
     */
    getDictionary() {
        return this.dict;
    }

    /**
     * Empties and recreate the content of the dictionary.
     * @param dict The content of the dictionary.
     */
    setDictionaryContent(dict) {
        this.dict.setContent(dict);
        this.persist()
    }

    importData(dictionary) {
        var importedTriples = "",
            dictContent = dictionary.dict;
        for (var graph in dictContent) {
            for (var triple in dictContent[graph]) {
                importedTriples += triple.replace(/(\n|\r|\\)/g, '') + "\n";
                for (var i = 0; i < dictContent[graph][triple].length; i++) {
                    dictContent[graph][triple][i].__proto__ = Fact.prototype;
                }
            }
        }
        this.setDictionaryContent(dictContent);
        return this.sm.load(importedTriples, "text/turtle")
    }

    persist() {
        if (!this.allowPersist && fs) return
        // const stack = new Error().stack;
        // console.log("====== HYLAR persist. This is not really an error, just a stack trace",stack);
        var dbDir = this.dbDir || './db';
        // Check if db folder exists
        if (!fs.existsSync(dbDir)){
            fs.mkdirSync(dbDir)
        }

        let dbconf = {
            mappingsGraphDbFiles: {},
            customRules: []
        }

        if (fs.existsSync(dbDir+'/db.conf')) {
            dbconf = Object.assign(dbconf, JSON.parse(fs.readFileSync(dbDir+'/db.conf').toString()))
        }

        dbconf.customRules = this._customRules.map((r => { return { name: r.name, content: r.toString() } }))

        for (let graphUri in this.getDictionary().dict) {
            // Write db content on file
            let filename = `${graphUri.match(RegularExpressions.URI_AFTER_HASH_OR_SLASH)[0]}.n3`
            let dbfilename = `${dbDir}/${filename}`
            let graphContent = this.getDictionary().dict[graphUri]
            let explicitEntries = []

            for (let triple in graphContent) {
                if (Logics.getOnlyExplicitFacts(graphContent[triple]).length > 0) explicitEntries.push(triple)
                if (this.EJSON) {
                    try {
                        const factJson = this.EJSON.stringify(graphContent[triple]);
                    }
                    catch (e) {
                        console.log(util.inspect(graphContent[triple],false,4));
                        throw e;
                    }
                }
            }
            fs.writeFileSync(dbfilename, explicitEntries.join('\n'))

            dbconf.mappingsGraphDbFiles[filename] = graphUri
        }

        fs.writeFileSync(dbDir+'/db.conf', JSON.stringify(dbconf, null, 3))
    }

    async restore() {
        this.restored = undefined;
        var dbDir = this.dbDir || './db';
        if (!fs || !fs.existsSync(dbDir) || !this.allowPersist) return
        let files  = fs.readdirSync(dbDir)
        if (!files.length) {
            Hylar.notify("No db files to recover.");
            return;
        }

        Hylar.notify('... Recovering DB from '+dbDir+'...')

        let dbconf = {
            mappingsGraphDbFiles: {},
            customRules: []
        }

        if (fs.existsSync(dbDir+'/db.conf')) {
            dbconf = Object.assign(dbconf, JSON.parse(fs.readFileSync(dbDir+'/db.conf').toString()))
        }

        // turn off reasoning before loading
        var wasReasoning = this.reasoning;
        this.reasoning = false;

        for (let file of files.filter((file) => {
            return file != 'db.conf' && file[0] !== '.';
        })) {
            try {
                let content = fs.readFileSync(`${dbDir}/${file}`).toString()
                for (let rule of dbconf.customRules) {
                    this.addRule(Logics.parseRule(rule.content, rule.name))
                }
                await this.load(content, 'text/n3', true, dbconf.mappingsGraphDbFiles[file])
            } catch (err) {
                Hylar.displayWarning(Errors.DBParsing(file));
                // don't continue
                throw err;
            }
        }

        this.restored = true;
        this.reasoning = wasReasoning;
        Hylar.notify('* DB recover finished *')
    }

    /**
     * Because restore is called in a non-async constructor,
     * this is necessary for initializing clients to know if
     * db is restored on construction.
     * @returns {Promise<boolean|*>}
     */
    async isRestored() {
        while (this.restored === undefined) {
            await (new Promise((resolve,reject) => {
                setTimeout(function() {
                    resolve();
                },500);
            }));
        }
        return this.restored;
    }

    checkConsistency() {
        var __FALSE__ = this.getDictionary().dict['#default']['__FALSE__'],
            isConsistent = true, inconsistencyReasons;

        if (__FALSE__ !== undefined) {
            if ( (this.isIncremental()) || (this.isTagBased() && __FALSE__[0].isValid()) ) {
                isConsistent = false;
                inconsistencyReasons = __FALSE__.causedBy;
            }
        }

        return {
            consistent: isConsistent,
            trace: inconsistencyReasons
        }
    }

    isTagBased() {
        return (this.rMethod == Reasoner.process.it.tagBased);
    }

    isIncremental() {
        return (this.rMethod == Reasoner.process.it.incrementally);
    }

    /**
     * Processes update queries.
     * @param sparql The query text.
     * @returns {Object} The results of this query.
     */
    async treatUpdate(update, type, syncCB, persistDerivations, whitelist) {
        syncCB = syncCB || function(result) {};
        if (typeof persistDerivations === "undefined") persistDerivations = true;
        Hylar.notify("Start update with persist: " + persistDerivations);
        let graph = update.name,
            iTriples = [],
            dTriples = [],
            FeIns, FeDel,
            F = this.getDictionary().values(graph),
            deleteQueryBody, promises = [],
            initialResponse = Utils.emptyPromise([ { triples:[] } ]);

        if(type == 'insert') {
            Hylar.notify('Starting insertion.');
            iTriples = iTriples.concat(update.triples);
        } else if(type  == 'delete') {
            Hylar.notify('Starting deletion.');
            for (var i = 0; i < update.triples.length; i++) {
                if (Utils.tripleContainsVariable(update.triples[i])) {
                    deleteQueryBody = ParsingInterface.tripleToTurtle(update.triples[i]);
                    const statement = 'CONSTRUCT { ' + deleteQueryBody + " }  WHERE { " + deleteQueryBody + " }";
                    promises.push(this.sm.query(statement));
                } else {
                    dTriples.push(update.triples[i]);
                }
            }

            initialResponse = Promise.all(promises);
            let results = await initialResponse;

            for (var i = 0; i < results.length; i++) {
                dTriples = dTriples.concat(results[i].triples);
            }
        }
        // Hylar.notify('Starting ParsingInterface.triplesToFacts (iTriples).');
        FeIns = ParsingInterface.triplesToFacts(iTriples, true, (this.rMethod == Reasoner.process.it.incrementally));
        // Hylar.notify('Starting ParsingInterface.triplesToFacts (dTriples).');
        FeDel = ParsingInterface.triplesToFacts(dTriples, true, (this.rMethod == Reasoner.process.it.incrementally));
        let derivations;
        if (this.reasoning === false) {
            derivations = {
                additions: FeIns,
                deletions: FeDel
            }
        }
        else {
            const startReasoning = Date.now();
            // experiment with passing dict to Reasoner, so that reasoner can use index
            // this.axioms appears to be unused
            const KB = F.concat(this.axioms);
            Hylar.notify(`Starting Reasoner.evaluate. ${FeIns.length} inserted. ${FeDel.length} deleted. ${KB.length} existing facts.`);
            derivations = await Reasoner.evaluate(FeIns, FeDel, this.dict, this.rMethod, this.rules, whitelist);
            const endReasoning = Date.now();
            Hylar.notify(`Finished Reasoner.evaluate in ${Math.round((endReasoning-startReasoning)/1000)} seconds.`);
        }
        let _inserted = [];
        let _deleted = [];
        if (derivations && derivations.additions) {
            _inserted = derivations.additions.map(f => f.asString);
        }
        if (derivations && derivations.deletions) {
            _deleted = derivations.deletions.map(f => f.asString);
        }
        console.log("Inserted", _inserted);
        console.log("Deleted", _deleted);

        let result;
        // Only actually update the fact store if we intend to
        if (persistDerivations === true) {
            this.registerDerivations(derivations, graph);

            let updates = {
                insert: ParsingInterface.factsToTurtle(derivations.additions),
                delete: ParsingInterface.factsToTurtle(derivations.deletions)
            }

            if(updates.delete != '') {
                result = this.sm.delete(updates.delete, graph);
            }
            if(updates.insert != '') {
                result = this.sm.insert(updates.insert, graph);
            }
        }

        // Use callback to pass derivations back up the chain to the external application
        syncCB(derivations);
        if (result) {
            return result;
        }
        return true
    }


    /**
     * Processes select or construct queries.
     * @param query The query text.
     * @returns {Object} The results of this query.
     */
    async treatSelectOrConstruct(query) {
        if (this.rMethod == Reasoner.process.it.tagBased) {
            let parsedQuery= ParsingInterface.parseSPARQL(query),
                graph = parsedQuery.where[0].name,
                constructEquivalentQuery = ParsingInterface.constructEquivalentQuery(query, graph);

            let results = await this.sm.query(constructEquivalentQuery)
            let triples = results.triples;
            let val = this.dict.findValues(triples, graph);
            let facts = val.found;

            let formattedResults = {
                results: results,
                filtered: Reasoner.engine.tagFilter(facts, this.dict.values(graph))
            }

            let temporaryData = this.dict.findKeys(formattedResults.filtered, graph).found.join(' ');
            return this.sm.loadIntoSideStore(temporaryData, graph);
        } else {
            return this.sm.query(query);
        }
    }

    /**
     * Registers newly inferred derivations
     * in the Dictionary.
     * @param derivations The derivations to be registered.
     */
    registerDerivations(derivations, graph) {
        let factsToBeAdded = derivations.additions,
            factsToBeDeleted = derivations.deletions;
        graph = this.dict.resolveGraph(graph);
        Hylar.notify('Registering derivations to dictionary...');

        for (let i = 0; i < factsToBeDeleted.length; i++) {
            if (factsToBeDeleted[i].toString() == 'IFALSE') {
                delete this.dict.dict[graph]['__FALSE__'];
            } else {
                delete this.dict.dict[graph][ParsingInterface.factToTurtle(factsToBeDeleted[i])];
            }
        }

        for (var i = 0; i < factsToBeAdded.length; i++) {
            this.dict.put(factsToBeAdded[i], graph);
            //Prefixes.registerPrefixFrom(factsToBeAdded[i])
        }

        this.persist()
        Hylar.success('Registered successfully.');
    }

    /**
     * Classifies the ontology
     * already loaded in the triplestore.
     * @returns {*}
     */
    async classify(graph) {
        const start = Date.now();
        Hylar.notify('Classification started.');

        let r = await this.sm.query('CONSTRUCT { ?a ?b ?c } WHERE { ?a ?b ?c }')
        let facts = []

        for (let i = 0; i <  r.triples.length; i++) {
            let triple = r.triples[i];
            // this was doing it wrong! this.dict.get(triple)
            const ttl = ParsingInterface.tripleToTurtle(triple);
            let _fs = this.dict.get(ttl);
            if(!_fs) {
                let f = ParsingInterface.tripleToFact(triple, true, (this.rMethod == Reasoner.process.it.incrementally))
                this.dict.put(f, graph)
                facts.push(f)
            } else facts = facts.concat(_fs)
        }

        const filteredFacts = [];
        for (let n = 0; n < facts.length; n++) {
            const fact = facts[n];
            if (fact.predicate[0] === `"`) {
                // did reasoner do this?
                console.log("BAD PREDICATE BEFORE REASONER:",fact);
                continue;
            }
            switch (fact.predicate) {
                case "http://www.w3.org/2000/01/rdf-schema#subClassOf":
                case "http://www.w3.org/1999/02/22-rdf-syntax-ns#type":
                    if (fact.object[0] === '"') {
                        // did reasoner do this?
                        console.log("BAD FACT BEFORE REASONER:", fact);
                        // for ^^xsd literals with abs uris in <> or not.
                        // I've seen both "97"^^<http://www.w3.org/2001/XMLSchema#integer>
                        // and "97"^^http://www.w3.org/2001/XMLSchema#integer
                        let rr = fact.object.match(/^"([\s\S]*)"\^\^.+#<?(\S+)>?/);
                        if (!rr) {
                            // for ^^xsd literals like "String Literal"^^xsd:string
                            rr = fact.object.match(/^"([\s\S]*)"\^\^xsd:(\S+)/);
                        }
                        if (rr) {
                            fact.object = rr[1];
                            console.log(`AFTER fix: ${fact.object}`);
                        } else {
                            console.log("Discard fact",fact);
                            break;
                        }
                    }
                default:
                    filteredFacts.push(fact);
            }
        }

        let derivations = await Reasoner.evaluate(filteredFacts, [], this.dict, this.rMethod, this.rules);
        if (this.classifyCallback) {
            this.classifyCallback(derivations);
        }
        this.registerDerivations(derivations, graph);

        console.log(`additions before filtering ${derivations.additions.length}`);
        const filteredAdditions = [];
        for (let n = 0; n < derivations.additions.length; n++) {
            const fact = derivations.additions[n];
            if (fact.predicate[0] === `"`) {
                // did reasoner do this?
                console.log("BAD PREDICATE AFTER REASONER:",fact);
                continue;
            }
            switch (fact.predicate) {
                case "http://www.w3.org/2000/01/rdf-schema#subClassOf":
                case "http://www.w3.org/1999/02/22-rdf-syntax-ns#type":
                    if (fact.object[0] === '"') {
                        // did reasoner do this?
                        // console.log("BAD FACT AFTER REASONER:",fact);
                        // why didn't this work?
                        derivations.additions.splice(n,1);
                    }
                    break;
                default:
                    filteredAdditions.push(fact);
            }
        }
        console.log(`additions after filtering ${derivations.additions.length}`);
        console.log(`filtered additions ${filteredAdditions.length}`);
        derivations.additions = filteredAdditions;

        let chunks = [], chunksNb = 200;
        for (var i = 0, j = derivations.additions.length; i < j; i += chunksNb) {
            let factsChunk = derivations.additions.slice(i,i+chunksNb);
            chunks.push(ParsingInterface.factsToTurtle(factsChunk));
        }

        Hylar.notify(`Begin inserting ${derivations.additions.length} triples in ${chunks.length} chunks into store.`);
        fs.writeFileSync("/tmp/hylar-chunks",``);
        let ct = 1;
        await Promise.reduce(chunks, (previous, chunk) => {
            console.log(`this.sm.insert chunk ${++ct}`);
            fs.appendFileSync("/tmp/hylar-chunks",`\n === chunk ${ct} ===\n`);
            fs.appendFileSync("/tmp/hylar-chunks",chunk);
            return this.sm.insert(chunk);
        }, 0)
        const end = Date.now()
        Hylar.notify(`Classification succeeded in ${Math.round((end-start)/1000)} seconds.`);
        emitter.emit('classif-ended');
        return true
    }

    async recomputeClosure(explicit = true) {

        let fullExplicitGraphs = explicit ? this.dict.explicitGraphs() : this.dict.allGraphsAsTtl();
        await this.clean()

        // JD - Found edge case failure here in rdfstore.js, failure to handle promise error
        // Just re-cleaning it appears to work, but allow multiple attempts
        // Secondary attempt
        if (typeof this.sm.storage === "undefined") {
          console.log("Storage error detected, re-attempting cleaning");
          await this.clean();
        }
        // Tertiary attempt
        if (typeof this.sm.storage === "undefined") {
          console.log("Storage error detected, re-attempting cleaning");
          await this.clean();
        }

        for (let graph of fullExplicitGraphs) {
            await this.load(graph.content, 'text/turtle', true, graph.name)
        }
    }

    /**
     * Load the RDF store from all Facts in all graphs,
     * both explicit and inferred. Graphs remain untouched.
     * This is specifically useful to restore a fully
     * working hylar reasoner and sparql engine from a
     * saved Facts collection.
     * @returns {Promise<void>}
     */
    async loadStoreFromGraphs() {
        const allGraphs = this.dict.allGraphsAsTtl();
        for (let graph of allGraphs) {
            // graph.name is only relevant when saving Facts to the graph,
            // the rdfstore doesn't care.
            // put in line breaks for easier parse debugging:
            let content = graph.content.replace(/ \. /g," . \n");
            // rdfstore freaks out at \
            content = content.replace(/\\/g,"/");
            fs.writeFileSync("/tmp/graph.txt",content);
            let rCt = await this.sm.load(content, "text/turtle");
            console.log(`${rCt} triples loaded in the store`);

            Hylar.notify(rCt + ' triples loaded in the store.', {  })

        }
    }

    /**
     * Add rules to the reasoner for
     * the next inferences.
     * @param ruleSet
     */
    async addRules(ruleSet) {
        this._customRules.push(...ruleSet)
        await this.recomputeClosure()
    }

    async addRule(rule) {
        // If the rule (by name) is already in the list, replace it
        if (!this._customRules.some((r,i) => {
            if (r.name === rule.name) {
                this._customRules[i] = rule;
                return true;
            }
        })) {
            this._customRules.push(rule)
        }
        // addRule should not recompute closure, because it gets called
        // multiple times by restore(), and also recomputeClosure calls persist,
        // which can wipe out our db before we've even loaded it.
        // await this.recomputeClosure()
    }

    async parseAndAddRule(rawRule, name) {
        var rule;
        try {
            rule = Logics.parseRule(rawRule, name);
        } catch(e) {
            Hylar.displayError('Error when parsing rule ' + rule);
            return;
        }
        await this.addRule(rule)
    }

    async removeRuleByName(name) {
        this._customRules = this._customRules.filter((rule) => {
            return rule.name != name
        })
        await this.recomputeClosure()
    }

    addToQueryHistory(query, noError) {
        this.queryHistory.push({ query: query, noError: noError });
    }

    async resetRules() {
        this._customRules = [];
        await this.recomputeClosure()
    }

    quiet() {
        Hylar.notify = function(){};
    }
}



module.exports = Hylar;
