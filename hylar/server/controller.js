/**
 * Created by Spadon on 02/10/2014.
 */

const fs = require("fs"),
  path = require("path"),
  mime = require("mime-types");

const H = require("../hylar");
const Logics = require("../core/Logics/Logics");
const ContentNegotiator = require("./content_negotiator");
const ParsingInterface = require("../core/ParsingInterface");

const appDir = path.dirname(require.main.filename),
  htmlDir = appDir + "/views";
let ontoDir = appDir + "/ontologies",
  port = 3000,
  parsedPort,
  contextPath = "";

let persistent = true;
let entailment = "owl2rl";
let dbDir;
let restore = false;
let reasoning = true;

console.log(process.argv);

process.argv.forEach(function(value, index) {
  if ((value === "--no-persist")) {
    persistent = false;
  }
});

process.argv.forEach(function(value, index) {
  if ((value === "--entailment") || (value === "-e")) {
    entailment = process.argv[index + 1];
  }
});

process.argv.forEach(function(value, index) {
  if (value === "--dbDir") {
    dbDir = process.argv[index + 1];
  }
});

process.argv.forEach(function(value, index) {
  if (value === "--restore") {
    restore = true;
  }
});

process.argv.forEach(function(value, index) {
  if (value === "--reasoning") {
    reasoning = !process.argv[index + 1].match(/false|0/i);
  }
});

const Hylar = new H({
  persistent, entailment, dbDir, reasoning
});

if (restore) {
  // eslint-disable-next-line no-new,no-async-promise-executor
  new Promise(async (resolve, reject) => {
    console.log("Hylar.restore()");
    const wasPersist = !!Hylar.allowPersist;
    Hylar.allowPersist = true;
    await Hylar.restore();
    Hylar.allowPersist = wasPersist;
    if (reasoning) {
      await Hylar.classify();
    }
  });
}

process.argv.forEach(function(value, index) {
  if ((value === "-od") || (value === "--ontology-directory") || (value === "-gd") || (value === "--graph-directory")) {
    ontoDir = path.resolve(process.argv[index + 1]);
  }
});

process.argv.forEach(function(value, index) {
  if ((value === "-p") || (value === "--port")) {
    parsedPort = parseInt(process.argv[index+1]);
    if (!Number.isNaN(parsedPort) && parsedPort > 0) {
      port = parsedPort;
    }
  }
});

process.argv.forEach(function(value, index) {
  if ((value === "-rm") || (value === "--reasoning-method")) {
    if (["tagBased", "tag-based"].includes(process.argv[index + 1])) {
      Hylar.setTagBased();
    }
    else {
      Hylar.setIncremental();
    }
  }
});

process.argv.forEach(function(value, index) {
  if ((value === "-cp") || (value === "--context-path")) {
    contextPath = "/" + process.argv[index + 1];
    console.log(contextPath);
  }
});

process.argv.forEach(function(value, index) {
  if ((value === "-x") || (value === "--reasoning-off")) {
    Hylar.setReasoningOff();
  }
});

module.exports = {

    /**
     * Server configuration
     */
  configuration: {
    appDir: appDir,
    ontoDir: ontoDir,
    port: port
  },

  status: function(req, res) {
    res.status(200).json({
      lastLog: Hylar.lastLog()
    });
  },

    /**
     * OWL File content to text
     * @param req
     * @param res
     * @param next
     */
  getOntology: function(req, res, next) {
    const initialTime = req.query.time,
      receivedReqTime = new Date().getTime(),
      filename = req.params.filename,
      absolutePathToFile = ontoDir + "/" + filename,
      extension = path.extname(absolutePathToFile),
      contentType = mime.contentType(extension);

    if (contentType) {
      req.mimeType = contentType.replace(/;.*/g, "");
    }
    else {
      req.mimeType = contentType;
    }

    req.requestDelay = receivedReqTime - initialTime;

    fs.readFile(absolutePathToFile, function(err, data) {
      if (err) {
        res.status(500).send(err.toString());
      }
      else {
        req.rawOntology = data.toString().replace(/(&)([a-z0-9]+)(;)/gi, "$2:");
        next();
      }
    });
  },

  loadOntology: async function(req, res, next) {
    const rawOntology = req.rawOntology,
      mimeType = req.mimeType,
      graph = req.graph,
      initialTime = new Date().getTime();

    try {
      await Hylar.load(rawOntology, mimeType, req.query.keepoldvalues, graph, req.body.reasoningMethod);
      req.processingDelay = new Date().getTime() - initialTime;
      H.success(`Classification of ${req.params.filename} finished in ${req.processingDelay} ms.`);
      next();

    }
    catch (error) {
      H.displayError(error);
      res.status(500).send(error.stack);
    }
  },

  escapeStrOntology: function(req, res, next) {
    req.rawOntology = req.body.content.replace(/(&)([a-z0-9]+)(;)/gi, "$2:");
    req.mimeType = req.body.mimetype;
    req.graph = req.body.graph;
    next();
  },

  acknowledgeEnd: function(req, res) {
    res.send(true);
  },

  sendHylarContents: function(req, res) {
    res.status(200).json({
      dictionary: Hylar.getDictionary(),
      processingDelay: req.processingDelay,
      requestDelay : req.requestDelay,
      serverTime : new Date().getTime()
    });
  },

  importHylarContents: async function(req, res) {
    let importedData;
    fs.readFile(ontoDir + "/export.json", async function(err, data) {
      if (err) {
        res.status(500).send(err.toString());
      }
      else {
        importedData = data.toString();
        try {
                    // Hylar.import doesn't exist!
          const value = await Hylar.import(JSON.parse(importedData).dictionary);
          res.send({status: value});
        }
        catch (_err) {
          res.status(500).json({err: _err.toString});
        }
      }
    });
  },

    /**
     * End-method returning an ontology
     * @param req
     * @param res
     */
  sendOntology: function(req, res) {
    if (req.headers.accept === "application/json") {
      res.header("Content-Type", "application/json");
      res.status(200).json({
        data: {
          ontologyTxt: req.rawOntology,
          mimeType: req.mimeType
        },
        requestDelay: req.requestDelay,
        serverTime: new Date().getTime()
      });
    }
    else {
      res.header("Content-Type", req.mimeType);
      res.status(200).send(req.rawOntology);
    }
  },

  removeOntology: function(req, res, next) {
    fs.unlinkSync(ontoDir + "/" + req.params.filename);
    H.notify(`File ${req.params.filename} removed`);
    next();

  },

  processSPARQL: async function(req, res) {
    let results = {};
    const asTTL = req.body.asTTL || req.query.asTTL;
    const initialTime = req.query.time,
      receivedReqTime = new Date().getTime(),
      requestDelay = receivedReqTime - initialTime;
    let processedTime = -1;

        // Actual sparql query
    const query = req.body.query || req.body.update || req.query.query;
    console.log("query", query);
    // Drop it if the query is null
    if (!query) ContentNegotiator.answerSparqlWithContentNegotiation(req, res);
    try {
      const parsedQuery = ParsingInterface.parseSPARQL(query);
      // Process query if it is set
      // Check if facts are requested
      const asFacts = req.body.asFacts || req.query.asFacts;
      let facts = [];
      if (asFacts) {
        if (parsedQuery.type !== "query") {
                    // For non-query type, use classifyCallback
          Hylar.classifyCallback = (factArray) => {
            facts = factArray.map(fact => ({
              subject: Hylar.prefixes.replaceUriWithPrefix(fact.subject),
              predicate: Hylar.prefixes.replaceUriWithPrefix(fact.predicate),
              object: Hylar.prefixes.replaceUriWithPrefix(fact.object),
              isValid: fact.isValid(),
              explicit: fact.explicit,
              causedBy: fact.causedBy,
              asString: fact.asString
            }));
          };
        }
      }
      results = await Hylar.query(query, req.body.reasoningMethod);
      processedTime = new Date().getTime();

      const hylar_meta = {
        processingDelay: processedTime - receivedReqTime,
        requestDelay: requestDelay,
        serverTime: new Date().getTime()
      };
      const totalTime = processedTime - receivedReqTime;

      H.success("Evaluation finished in " + (totalTime) + "ms.");

      Hylar.addToQueryHistory(req.body.query, true);

      if (asFacts) {
                // Clear the callback if it was set
        Hylar.classifyCallback = null;

                // For query type, look up facts in dictionary using bindings
        if (parsedQuery.type === "query") {
          const bgp = parsedQuery.where.find(w => w.type === "bgp");
          if (bgp) {
            results.forEach((binding) => {
              bgp.triples.forEach((triple) => {
                const s = binding[triple.subject.substring(1)].value;
                const p = triple.predicate;
                const o = binding[triple.object.substring(1)].value;
                if (s && p && o) {
                                    // Look up fact in dictionary
                  const match = Hylar.dict.getIndex(s, p, o);
                  if (match.length) {
                    const fact = match[0];
                    facts.push({
                      subject: fact.subject,
                      predicate: fact.predicate,
                      object: fact.object,
                      isValid: fact.isValid,
                      explicit: fact.explicit,
                      causedBy: fact.causedBy,
                      asString: fact.asString
                    });
                  }
                }
              });
            });
          }
        }

        res.status(200).json({
          facts: facts,
          meta: hylar_meta
        });
      }
      else if (asTTL) {
                // Convert binding maps to triples using the WHERE clause structure
        let ttlOutput = "";
        if (parsedQuery.queryType === "SELECT") {
          const bgp = parsedQuery.where.find(w => w.type === "bgp");
          if (bgp) {
            results.forEach((binding) => {
              bgp.triples.forEach((triple) => {
                const s = binding[triple.subject.substring(1)].value; // Remove ? prefix
                const p = triple.predicate;
                const o = binding[triple.object.substring(1)].value; // Remove ? prefix
                if (s && p && o) {
                  ttlOutput += `<${s}> <${p}> <${o}> .\n`;
                }
              });
            });
          }
        }
        res.header("Content-Type", "text/turtle");
        res.status(200).send(ttlOutput);
      }
      else {
        ContentNegotiator.answerSparqlWithContentNegotiation(req, res, { results, totalTime });
      }
    }
    catch (error) {
      Hylar.addToQueryHistory(req.body.query, false);
      res.status(500).send(error.message);
    }
  },

  list: function(req, res) {
    res.send(fs.readdirSync(ontoDir));
  },

    /**
     * Simple HelloWorld
     * @param req
     * @param res
     */
  hello: function(req, res) {
    const ontologies = fs.readdirSync(ontoDir), kb = Hylar.getDictionary().values();

    res.render(htmlDir + "/pages/index", {
      kb: kb,
      ontologies: ontologies,
      contextPath: contextPath,
      entailment: Hylar.entailment.toUpperCase()
    });
  },

    /**
     * CORS Middleware
     * @param req
     * @param res
     */
  allowCrossDomain: function(req, res, next) {
    res.header("Access-Control-Allow-Origin", "*");
    res.header("Access-Control-Allow-Methods", "GET,PUT,POST,DELETE");
    res.header("Access-Control-Allow-Headers", "Content-Type");
    next();
  },

    /** Current server time */
  time: function(req, res) {
    res.status(200).json({
      ms: new Date().getTime()
    });
  },

  upload: function(req, res, next) {
    fs.renameSync(req.file.path, path.normalize(req.file.destination + "/" + req.file.originalname));
    res.status(200).json({
      fileName: req.file.originalname
    });
    H.notify(`File ${req.file.originalname} loaded and ready to process`);
  },

  renderFacts: function(req, res) {
    const dict = Hylar.getDictionary();
    const content = dict.content();
    const graph = decodeURIComponent(req.params.graph);
    const consistent = Hylar.checkConsistency().consistent;

    const prepareFactForPresentation = (fact, _graph) => {
      return {
        _graph,
        asString: fact.asString,
        rule: fact.rule,
        subject: Hylar.prefixes.replaceUriWithPrefix(fact.subject),
        predicate: Hylar.prefixes.replaceUriWithPrefix(fact.predicate),
        object: Hylar.prefixes.replaceUriWithPrefix(fact.object),
        isValid: fact.isValid(),
        isAxiom: fact.isAxiom,
        explicit: fact.explicit,
        causedBy: fact.causedBy,
        _self: fact
      };
    };

    const kb = [];

    for (const __graph in content) {
      for (const dictKey in content[__graph]) {
        const values = dict.get(dictKey, __graph);
        for (let i = 0; i < values.length; i++) {
          kb.push(prepareFactForPresentation(values[i], __graph));
        }
      }
    }

    const axioms = Hylar.axioms.map((axiom) => {
      return prepareFactForPresentation(axiom, "_:axiomatic_triples");
    });

    res.render(htmlDir + "/pages/explore", {
      kb: kb.concat(axioms),
      graph: graph,
      contextPath: contextPath,
      consistent,
      entailment: Hylar.entailment.toUpperCase(),
      axioms,
      isTagBased: Hylar.reasoningMethod === "tagBased"
    });
  },

  simpleSparql: async function(req, res, next) {
        //noinspection JSValidateTypes
    const start = new Date().getTime();
    let processingDelay;
    if (req.body.query !== undefined) {
      try {
        const result = await Hylar.query(req.body.query);
        processingDelay = new Date().getTime() - start;
        H.success("Evaluation finished in " + processingDelay + "ms.");
        req.sparqlResults = result;
        req.sparqlQuery = req.body.query;
        Hylar.addToQueryHistory(req.sparqlQuery, true);
        next();
      }
      catch (e) {
        Hylar.addToQueryHistory(req.body.query, false);
        req.error = e;
        next();
      }
    }
    else {
      next();
    }
  },

  sparqlInterface: function(req, res) {
    res.render(htmlDir + "/pages/sparql", {
      sparqlQuery: (req.sparqlQuery ? req.sparqlQuery : "SELECT * { ?s ?p ?o . }"),
      prevResults: (req.sparqlResults ? req.sparqlResults : ""),
      history: Hylar.queryHistory,
      error: (req.error ? req.error: ""),
      contextPath: contextPath
    });
  },

  renderRules: function(req, res) {
    res.render(htmlDir + "/pages/rules", {
      prefixes: Hylar.prefixes.entries(),
      rules: Hylar.getRulesAsStringArray(),
      error: req.error,
      contextPath: contextPath
    });
  },

  addRules: async function(req, res, next) {
    const rules = req.body.rules;
    let parsedRules;
    if (req.body.rule !== undefined) {
      try {
        await Hylar.addRule(Logics.parseRule(req.body.rule, req.body.rulename));
        next();
      }
      catch (e) {
        res.status(500).send(e.stack);
      }
    }
    else {
      try {
        parsedRules = Logics.parseRules(rules);
        await Hylar.addRules(parsedRules);
        next();
      }
      catch (e) {
        res.status(500).send(e.stack);
      }
    }
  },

  resetRules: async function(req, res, next) {
    await Hylar.resetRules();
    next();
  },

  removeRule: async function(req, res, next) {
    const name = req.params.name;
    await Hylar.removeRuleByName(name);
    next();
  },

  listRules: function(req, res) {
    res.json({"rules": Hylar.rules.toString()});
  },

  resetKB: function(req, res, next) {
    Hylar.clean();
    next();
  },
};
