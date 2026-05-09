/* eslint-disable */
/**
 * Created by Spadon on 13/02/2015.
 */

var q = require('q');
var md5 = require('md5');

var RegularExpressions = require('./RegularExpressions');
var EventEmitter = require('events').EventEmitter;

/** Event emitter */

var emitter = new EventEmitter();

emitter.on('started', function(task) {
    console.log('started ' + task);
});

emitter.on('finished', function(task) {
    console.log('processed ' + task);
});

Utils = {

    _instanceid: 1,

    emitter: emitter,

    /**
     * Returns a set of elements
     * with distinct string representation.
     * @param _set1
     * @param _set2
     * @returns {Array}
     */
    // Prefer Fact.asString (already cached in the constructor) and fall back
    // to toString() so the function still works on arbitrary values
    // (e.g. Rule.constants, which are strings). See optimization-spec.md §3.2.
    _key: function(el) {
        return el.asString !== undefined ? el.asString : el.toString();
    },

    uniques: function(...sets) {
        var map = new Map();
        for (var s = 0; s < sets.length; s++) {
            var set = sets[s];
            if (!set) continue;
            for (var i = 0; i < set.length; i++) {
                var el = set[i];
                if (el !== undefined) {
                    map.set(Utils._key(el), el);
                }
            }
        }
        return Array.from(map.values());
    },

    insertUnique: function(_set, val) {
        if (val === undefined) return _set ? _set.slice() : [];
        if (!_set || _set.length === 0) return [val];
        var key = Utils._key(val);
        var out = new Array(_set.length);
        var replaced = false;
        for (var i = 0; i < _set.length; i++) {
            var el = _set[i];
            // Match uniques(): last write wins on duplicate key.
            if (!replaced && el !== undefined && Utils._key(el) === key) {
                out[i] = val;
                replaced = true;
            } else {
                out[i] = el;
            }
        }
        if (!replaced) out.push(val);
        return out;
    },

    // Equivalent to uniques(_set1, _set2).length == _set1.length but avoids
    // materializing the union array.
    containsSubset: function(_set1, _set2) {
        var keys = new Set();
        if (_set1) {
            for (var i = 0; i < _set1.length; i++) {
                var el = _set1[i];
                if (el !== undefined) keys.add(Utils._key(el));
            }
        }
        if (_set2) {
            for (var i = 0; i < _set2.length; i++) {
                var el = _set2[i];
                if (el !== undefined) keys.add(Utils._key(el));
            }
        }
        return keys.size === (_set1 ? _set1.length : 0);
    },

    /**
     * Checks if a string is a variable,
     * @param str
     * @returns {boolean}
     */
    isVariable: function(str) {
        if (str === undefined) {
            return false;
        }
        try {
            return (str.indexOf('?') === 0);
        } catch(e) {
            return false;
        }
    },

    /**
     * Checks if a string is an operator (>, <, >=, <= or =)
     * @param str
     * @returns {boolean}
     */
    isOperator: function(str) {
        try {
            return ((str == '>') || (str == '<') || (str == '<=') || (str == '>=') || (str == '=='));
        } catch(e) {
            return false;
        }
    },

    removeBeforeSharp: function(str) {
        if (str.indexOf('#') === -1 || str.charAt(0) === '"') return str;
        var splitted = str.split('#');
        return /*splitted[0].slice(0,10) + '...#' + */splitted[1];
    },

    equivalentSets: function(s1, s2) {
        if (s1.toString() == s2.toString()) {
            return true;
        }
        if (s1.length != s2.length) {
            return false;
        }
        for (var i = 0; i < s1.length; i++) {
            if (this.notInSet(s2, s1[i])) {
                return false;
            }
        }
        return true;
    },

    notInSet: function(s1, elem) {
        return (s1.toString().indexOf(elem.toString()) === -1);
    },

    getValueFromDatatype: function(datatype) {
        var rawValueMatch = datatype.match(RegularExpressions.LITERAL_RAW_VALUE)[1],
           literalWithoutTypeMatch = datatype.match(RegularExpressions.LITERAL_WITHOUT_TYPE)[1];
        if (parseFloat(rawValueMatch) === NaN) {
            return literalWithoutTypeMatch;
        } else {
            return rawValueMatch;
        }
    },

    emptyPromise: function(toBeReturned) {
        var deferred = q.defer();
        deferred.resolve(toBeReturned);
        return deferred.promise;
    },

    tripleContainsVariable: function(triple) {
        if (this.isVariable(triple.subject)
            || this.isVariable(triple.predicate)
            || this.isVariable(triple.object)) {
            return true;
        }
        return false;
    },

    asCHRAtom: function(elem, mapping) {
        if(Logics.isVariable(elem)) {
            if(mapping[elem] === undefined) {
                if (mapping.__lastCHRVar) {
                    mapping.__lastCHRVar = String.fromCharCode(mapping.__lastCHRVar.charCodeAt(0)+1);
                } else {
                    mapping.__lastCHRVar = 'A';
                }
                mapping[elem] = mapping.__lastCHRVar;
            }
            return mapping[elem];
        } else {
            return '"' + elem.replace(/[^a-zA-Z]/g,'') + '"';
        }
    },

    stringHash: function(strings) {
        strings = Array.isArray(strings) ? strings : [strings];
        const str = strings.join('');
        return md5(str);
    }
}

module.exports = Utils
