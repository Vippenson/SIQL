window.PARSER = 
(function() {
  "use strict";

  function peg$subclass(child, parent) {
    function ctor() { this.constructor = child; }
    ctor.prototype = parent.prototype;
    child.prototype = new ctor();
  }

  function peg$SyntaxError(message, expected, found, location) {
    this.message  = message;
    this.expected = expected;
    this.found    = found;
    this.location = location;
    this.name     = "SyntaxError";

    if (typeof Error.captureStackTrace === "function") {
      Error.captureStackTrace(this, peg$SyntaxError);
    }
  }

  peg$subclass(peg$SyntaxError, Error);

  peg$SyntaxError.buildMessage = function(expected, found) {
    var DESCRIBE_EXPECTATION_FNS = {
          literal: function(expectation) {
            return "\"" + literalEscape(expectation.text) + "\"";
          },

          "class": function(expectation) {
            var escapedParts = "",
                i;

            for (i = 0; i < expectation.parts.length; i++) {
              escapedParts += expectation.parts[i] instanceof Array
                ? classEscape(expectation.parts[i][0]) + "-" + classEscape(expectation.parts[i][1])
                : classEscape(expectation.parts[i]);
            }

            return "[" + (expectation.inverted ? "^" : "") + escapedParts + "]";
          },

          any: function(expectation) {
            return "any character";
          },

          end: function(expectation) {
            return "end of input";
          },

          other: function(expectation) {
            return expectation.description;
          }
        };

    function hex(ch) {
      return ch.charCodeAt(0).toString(16).toUpperCase();
    }

    function literalEscape(s) {
      return s
        .replace(/\\/g, '\\\\')
        .replace(/"/g,  '\\"')
        .replace(/\0/g, '\\0')
        .replace(/\t/g, '\\t')
        .replace(/\n/g, '\\n')
        .replace(/\r/g, '\\r')
        .replace(/[\x00-\x0F]/g,          function(ch) { return '\\x0' + hex(ch); })
        .replace(/[\x10-\x1F\x7F-\x9F]/g, function(ch) { return '\\x'  + hex(ch); });
    }

    function classEscape(s) {
      return s
        .replace(/\\/g, '\\\\')
        .replace(/\]/g, '\\]')
        .replace(/\^/g, '\\^')
        .replace(/-/g,  '\\-')
        .replace(/\0/g, '\\0')
        .replace(/\t/g, '\\t')
        .replace(/\n/g, '\\n')
        .replace(/\r/g, '\\r')
        .replace(/[\x00-\x0F]/g,          function(ch) { return '\\x0' + hex(ch); })
        .replace(/[\x10-\x1F\x7F-\x9F]/g, function(ch) { return '\\x'  + hex(ch); });
    }

    function describeExpectation(expectation) {
      return DESCRIBE_EXPECTATION_FNS[expectation.type](expectation);
    }

    function describeExpected(expected) {
      var descriptions = new Array(expected.length),
          i, j;

      for (i = 0; i < expected.length; i++) {
        descriptions[i] = describeExpectation(expected[i]);
      }

      descriptions.sort();

      if (descriptions.length > 0) {
        for (i = 1, j = 1; i < descriptions.length; i++) {
          if (descriptions[i - 1] !== descriptions[i]) {
            descriptions[j] = descriptions[i];
            j++;
          }
        }
        descriptions.length = j;
      }

      switch (descriptions.length) {
        case 1:
          return descriptions[0];

        case 2:
          return descriptions[0] + " or " + descriptions[1];

        default:
          return descriptions.slice(0, -1).join(", ")
            + ", or "
            + descriptions[descriptions.length - 1];
      }
    }

    function describeFound(found) {
      return found ? "\"" + literalEscape(found) + "\"" : "end of input";
    }

    return "Expected " + describeExpected(expected) + " but " + describeFound(found) + " found.";
  };

  function peg$parse(input, options) {
    options = options !== void 0 ? options : {};

    var peg$FAILED = {},

        peg$startRuleFunctions = { FlattenedConfig: peg$parseFlattenedConfig },
        peg$startRuleFunction  = peg$parseFlattenedConfig,

        peg$c0 = function(c) { if (c.nameError == null && c.parseTree != null) {
               return {"nameError": c.nameError, "flattenedParseTree": flattenAll(c.parseTree)};
            } else {
               return {"nameError": c.nameError, "flattenedParseTree": null};
            }
          },
        peg$c1 = function(c) { var names = [];
              for (var i = 0;i < c.length; i++) {
                  var n = c[i].name;
                  var d = c[i].selector;
                  var error = checkVars (n, names, d);
                  if (error != null) {
                     return { "nameError":
                         "Error at " + n + ": " + error + " is not defined!"
                       , "parseTree": null};
                  }
                  if (names.indexOf(n)>=0) {
                      return { "nameError": "Error: " + n + " is already defined!"
                             , "parseTree":null };
                  } else {
                      names.push(n);
                  }
              }
              return {"nameError":null, "parseTree":c};
            },
        peg$c2 = ";",
        peg$c3 = peg$literalExpectation(";", false),
        peg$c4 = function(d, c) { return ([ d ].concat(c))},
        peg$c5 = function(d) {return [ d ]},
        peg$c6 = "=",
        peg$c7 = peg$literalExpectation("=", false),
        peg$c8 = function(n, s) {return {"name": n, "selector": s}},
        peg$c9 = "exclude",
        peg$c10 = peg$literalExpectation("exclude", false),
        peg$c11 = function(s) {return (new Exclude(s)) },
        peg$c12 = function(n) {return (new Var(n))},
        peg$c13 = function(f) {return (new Direct(f))},
        peg$c14 = "[",
        peg$c15 = peg$literalExpectation("[", false),
        peg$c16 = "]",
        peg$c17 = peg$literalExpectation("]", false),
        peg$c18 = function(ms) { return (new Sequence(ms))},
        peg$c19 = "everything",
        peg$c20 = peg$literalExpectation("everything", false),
        peg$c21 = function() { return [] },
        peg$c22 = "or",
        peg$c23 = peg$literalExpectation("or", false),
        peg$c24 = ",",
        peg$c25 = peg$literalExpectation(",", false),
        peg$c26 = function(s, ss) { return ([s].concat(ss)) },
        peg$c27 = function(s) { return [s] },
        peg$c28 = "*",
        peg$c29 = peg$literalExpectation("*", false),
        peg$c30 = "x",
        peg$c31 = peg$literalExpectation("x", false),
        peg$c32 = function(ps, q) {return {"predicates":ps, "quantity": new Exact(q)}},
        peg$c33 = "-",
        peg$c34 = peg$literalExpectation("-", false),
        peg$c35 = function(ps, q) {return {"predicates":ps, "quantity": new Exact(-q)}},
        peg$c36 = "none",
        peg$c37 = peg$literalExpectation("none", false),
        peg$c38 = function(ps) {return {"predicates":ps, "quantity": new Exact(0)}},
        peg$c39 = "all",
        peg$c40 = peg$literalExpectation("all", false),
        peg$c41 = function(ps) {return {"predicates":ps, "quantity": new All(null)}},
        peg$c42 = "-all",
        peg$c43 = peg$literalExpectation("-all", false),
        peg$c44 = function(ps) {return {"predicates":ps, "quantity": new NAll(null)}},
        peg$c45 = function(ps) {return {"predicates":ps, "quantity": new Exact(1)}},
        peg$c46 = "anyItem",
        peg$c47 = peg$literalExpectation("anyItem", false),
        peg$c48 = "and",
        peg$c49 = peg$literalExpectation("and", false),
        peg$c50 = "&",
        peg$c51 = peg$literalExpectation("&", false),
        peg$c52 = function(p, ps) {return ([p].concat(ps))},
        peg$c53 = function(p) {return [p]},
        peg$c54 = "name",
        peg$c55 = peg$literalExpectation("name", false),
        peg$c56 = function(m, s) {return {"field": "name", "mode": m, "value": s}},
        peg$c57 = "type",
        peg$c58 = peg$literalExpectation("type", false),
        peg$c59 = "is",
        peg$c60 = peg$literalExpectation("is", false),
        peg$c61 = function(t) {return {"field":"type", "mode": "==", "value": t}},
        peg$c62 = function(s) {return {"field":"name", "Mode": "==", "value":s}},
        peg$c63 = "==",
        peg$c64 = peg$literalExpectation("==", false),
        peg$c65 = "startsWith",
        peg$c66 = peg$literalExpectation("startsWith", false),
        peg$c67 = "contains",
        peg$c68 = peg$literalExpectation("contains", false),
        peg$c69 = "<=",
        peg$c70 = peg$literalExpectation("<=", false),
        peg$c71 = ">=",
        peg$c72 = peg$literalExpectation(">=", false),
        peg$c73 = ">",
        peg$c74 = peg$literalExpectation(">", false),
        peg$c75 = "<",
        peg$c76 = peg$literalExpectation("<", false),
        peg$c77 = "POWER_ARMOR",
        peg$c78 = peg$literalExpectation("POWER_ARMOR", false),
        peg$c79 = "WEAPON",
        peg$c80 = peg$literalExpectation("WEAPON", false),
        peg$c81 = "ARMOR",
        peg$c82 = peg$literalExpectation("ARMOR", false),
        peg$c83 = "APPAREL",
        peg$c84 = peg$literalExpectation("APPAREL", false),
        peg$c85 = "FOOD_WATER",
        peg$c86 = peg$literalExpectation("FOOD_WATER", false),
        peg$c87 = "AID",
        peg$c88 = peg$literalExpectation("AID", false),
        peg$c89 = "NOTES",
        peg$c90 = peg$literalExpectation("NOTES", false),
        peg$c91 = "HOLO",
        peg$c92 = peg$literalExpectation("HOLO", false),
        peg$c93 = "AMMO",
        peg$c94 = peg$literalExpectation("AMMO", false),
        peg$c95 = "MISC",
        peg$c96 = peg$literalExpectation("MISC", false),
        peg$c97 = "MODS",
        peg$c98 = peg$literalExpectation("MODS", false),
        peg$c99 = "JUNK",
        peg$c100 = peg$literalExpectation("JUNK", false),
        peg$c101 = /^[a-zA-Z]/,
        peg$c102 = peg$classExpectation([["a", "z"], ["A", "Z"]], false, false),
        peg$c103 = /^[a-zA-Z0-9]/,
        peg$c104 = peg$classExpectation([["a", "z"], ["A", "Z"], ["0", "9"]], false, false),
        peg$c105 = function(d, ds) { return d + ds.join('') },
        peg$c106 = /^[1-9]/,
        peg$c107 = peg$classExpectation([["1", "9"]], false, false),
        peg$c108 = /^[0-9]/,
        peg$c109 = peg$classExpectation([["0", "9"]], false, false),
        peg$c110 = function(n) {return Number(text())},
        peg$c111 = /^[ \t\n\r]/,
        peg$c112 = peg$classExpectation([" ", "\t", "\n", "\r"], false, false),
        peg$c113 = /^["]/,
        peg$c114 = peg$classExpectation(["\""], false, false),
        peg$c115 = /^[a-zA-Z0-9 ]/,
        peg$c116 = peg$classExpectation([["a", "z"], ["A", "Z"], ["0", "9"], " "], false, false),
        peg$c117 = function(s) {return s.join('')},

        peg$currPos          = 0,
        peg$savedPos         = 0,
        peg$posDetailsCache  = [{ line: 1, column: 1 }],
        peg$maxFailPos       = 0,
        peg$maxFailExpected  = [],
        peg$silentFails      = 0,

        peg$result;

    if ("startRule" in options) {
      if (!(options.startRule in peg$startRuleFunctions)) {
        throw new Error("Can't start parsing from rule \"" + options.startRule + "\".");
      }

      peg$startRuleFunction = peg$startRuleFunctions[options.startRule];
    }

    function text() {
      return input.substring(peg$savedPos, peg$currPos);
    }

    function location() {
      return peg$computeLocation(peg$savedPos, peg$currPos);
    }

    function expected(description, location) {
      location = location !== void 0 ? location : peg$computeLocation(peg$savedPos, peg$currPos)

      throw peg$buildStructuredError(
        [peg$otherExpectation(description)],
        input.substring(peg$savedPos, peg$currPos),
        location
      );
    }

    function error(message, location) {
      location = location !== void 0 ? location : peg$computeLocation(peg$savedPos, peg$currPos)

      throw peg$buildSimpleError(message, location);
    }

    function peg$literalExpectation(text, ignoreCase) {
      return { type: "literal", text: text, ignoreCase: ignoreCase };
    }

    function peg$classExpectation(parts, inverted, ignoreCase) {
      return { type: "class", parts: parts, inverted: inverted, ignoreCase: ignoreCase };
    }

    function peg$anyExpectation() {
      return { type: "any" };
    }

    function peg$endExpectation() {
      return { type: "end" };
    }

    function peg$otherExpectation(description) {
      return { type: "other", description: description };
    }

    function peg$computePosDetails(pos) {
      var details = peg$posDetailsCache[pos], p;

      if (details) {
        return details;
      } else {
        p = pos - 1;
        while (!peg$posDetailsCache[p]) {
          p--;
        }

        details = peg$posDetailsCache[p];
        details = {
          line:   details.line,
          column: details.column
        };

        while (p < pos) {
          if (input.charCodeAt(p) === 10) {
            details.line++;
            details.column = 1;
          } else {
            details.column++;
          }

          p++;
        }

        peg$posDetailsCache[pos] = details;
        return details;
      }
    }

    function peg$computeLocation(startPos, endPos) {
      var startPosDetails = peg$computePosDetails(startPos),
          endPosDetails   = peg$computePosDetails(endPos);

      return {
        start: {
          offset: startPos,
          line:   startPosDetails.line,
          column: startPosDetails.column
        },
        end: {
          offset: endPos,
          line:   endPosDetails.line,
          column: endPosDetails.column
        }
      };
    }

    function peg$fail(expected) {
      if (peg$currPos < peg$maxFailPos) { return; }

      if (peg$currPos > peg$maxFailPos) {
        peg$maxFailPos = peg$currPos;
        peg$maxFailExpected = [];
      }

      peg$maxFailExpected.push(expected);
    }

    function peg$buildSimpleError(message, location) {
      return new peg$SyntaxError(message, null, null, location);
    }

    function peg$buildStructuredError(expected, found, location) {
      return new peg$SyntaxError(
        peg$SyntaxError.buildMessage(expected, found),
        expected,
        found,
        location
      );
    }

    function peg$parseFlattenedConfig() {
      var s0, s1;

      s0 = peg$currPos;
      s1 = peg$parseValidConfig();
      if (s1 !== peg$FAILED) {
        peg$savedPos = s0;
        s1 = peg$c0(s1);
      }
      s0 = s1;

      return s0;
    }

    function peg$parseValidConfig() {
      var s0, s1;

      s0 = peg$currPos;
      s1 = peg$parseConfig();
      if (s1 !== peg$FAILED) {
        peg$savedPos = s0;
        s1 = peg$c1(s1);
      }
      s0 = s1;

      return s0;
    }

    function peg$parseConfig() {
      var s0, s1, s2, s3, s4, s5;

      s0 = peg$currPos;
      s1 = peg$parseDefinition();
      if (s1 !== peg$FAILED) {
        s2 = peg$parse_();
        if (s2 !== peg$FAILED) {
          if (input.charCodeAt(peg$currPos) === 59) {
            s3 = peg$c2;
            peg$currPos++;
          } else {
            s3 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c3); }
          }
          if (s3 !== peg$FAILED) {
            s4 = peg$parse_();
            if (s4 !== peg$FAILED) {
              s5 = peg$parseConfig();
              if (s5 !== peg$FAILED) {
                peg$savedPos = s0;
                s1 = peg$c4(s1, s5);
                s0 = s1;
              } else {
                peg$currPos = s0;
                s0 = peg$FAILED;
              }
            } else {
              peg$currPos = s0;
              s0 = peg$FAILED;
            }
          } else {
            peg$currPos = s0;
            s0 = peg$FAILED;
          }
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
      if (s0 === peg$FAILED) {
        s0 = peg$currPos;
        s1 = peg$parseDefinition();
        if (s1 !== peg$FAILED) {
          s2 = peg$parse_();
          if (s2 !== peg$FAILED) {
            if (input.charCodeAt(peg$currPos) === 59) {
              s3 = peg$c2;
              peg$currPos++;
            } else {
              s3 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c3); }
            }
            if (s3 !== peg$FAILED) {
              s4 = peg$parse_();
              if (s4 !== peg$FAILED) {
                peg$savedPos = s0;
                s1 = peg$c5(s1);
                s0 = s1;
              } else {
                peg$currPos = s0;
                s0 = peg$FAILED;
              }
            } else {
              peg$currPos = s0;
              s0 = peg$FAILED;
            }
          } else {
            peg$currPos = s0;
            s0 = peg$FAILED;
          }
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
      }

      return s0;
    }

    function peg$parseDefinition() {
      var s0, s1, s2, s3, s4, s5;

      s0 = peg$currPos;
      s1 = peg$parseName();
      if (s1 !== peg$FAILED) {
        s2 = peg$parse_();
        if (s2 !== peg$FAILED) {
          if (input.charCodeAt(peg$currPos) === 61) {
            s3 = peg$c6;
            peg$currPos++;
          } else {
            s3 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c7); }
          }
          if (s3 !== peg$FAILED) {
            s4 = peg$parse_();
            if (s4 !== peg$FAILED) {
              s5 = peg$parseSelector();
              if (s5 !== peg$FAILED) {
                peg$savedPos = s0;
                s1 = peg$c8(s1, s5);
                s0 = s1;
              } else {
                peg$currPos = s0;
                s0 = peg$FAILED;
              }
            } else {
              peg$currPos = s0;
              s0 = peg$FAILED;
            }
          } else {
            peg$currPos = s0;
            s0 = peg$FAILED;
          }
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }

      return s0;
    }

    function peg$parseSelector() {
      var s0, s1, s2, s3, s4, s5;

      s0 = peg$currPos;
      if (input.substr(peg$currPos, 7) === peg$c9) {
        s1 = peg$c9;
        peg$currPos += 7;
      } else {
        s1 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c10); }
      }
      if (s1 !== peg$FAILED) {
        s2 = peg$parse_();
        if (s2 !== peg$FAILED) {
          s3 = peg$parseSelector();
          if (s3 !== peg$FAILED) {
            peg$savedPos = s0;
            s1 = peg$c11(s3);
            s0 = s1;
          } else {
            peg$currPos = s0;
            s0 = peg$FAILED;
          }
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
      if (s0 === peg$FAILED) {
        s0 = peg$currPos;
        s1 = peg$parseName();
        if (s1 !== peg$FAILED) {
          peg$savedPos = s0;
          s1 = peg$c12(s1);
        }
        s0 = s1;
        if (s0 === peg$FAILED) {
          s0 = peg$currPos;
          s1 = peg$parseFilter();
          if (s1 !== peg$FAILED) {
            peg$savedPos = s0;
            s1 = peg$c13(s1);
          }
          s0 = s1;
          if (s0 === peg$FAILED) {
            s0 = peg$currPos;
            if (input.charCodeAt(peg$currPos) === 91) {
              s1 = peg$c14;
              peg$currPos++;
            } else {
              s1 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c15); }
            }
            if (s1 !== peg$FAILED) {
              s2 = peg$parse_();
              if (s2 !== peg$FAILED) {
                s3 = peg$parseSelectors();
                if (s3 !== peg$FAILED) {
                  s4 = peg$parse_();
                  if (s4 !== peg$FAILED) {
                    if (input.charCodeAt(peg$currPos) === 93) {
                      s5 = peg$c16;
                      peg$currPos++;
                    } else {
                      s5 = peg$FAILED;
                      if (peg$silentFails === 0) { peg$fail(peg$c17); }
                    }
                    if (s5 !== peg$FAILED) {
                      peg$savedPos = s0;
                      s1 = peg$c18(s3);
                      s0 = s1;
                    } else {
                      peg$currPos = s0;
                      s0 = peg$FAILED;
                    }
                  } else {
                    peg$currPos = s0;
                    s0 = peg$FAILED;
                  }
                } else {
                  peg$currPos = s0;
                  s0 = peg$FAILED;
                }
              } else {
                peg$currPos = s0;
                s0 = peg$FAILED;
              }
            } else {
              peg$currPos = s0;
              s0 = peg$FAILED;
            }
          }
        }
      }

      return s0;
    }

    function peg$parseSelectors() {
      var s0, s1, s2, s3, s4, s5;

      s0 = peg$currPos;
      if (input.substr(peg$currPos, 10) === peg$c19) {
        s1 = peg$c19;
        peg$currPos += 10;
      } else {
        s1 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c20); }
      }
      if (s1 !== peg$FAILED) {
        peg$savedPos = s0;
        s1 = peg$c21();
      }
      s0 = s1;
      if (s0 === peg$FAILED) {
        s0 = peg$currPos;
        s1 = peg$parseSelector();
        if (s1 !== peg$FAILED) {
          s2 = peg$parse_();
          if (s2 !== peg$FAILED) {
            if (input.substr(peg$currPos, 2) === peg$c22) {
              s3 = peg$c22;
              peg$currPos += 2;
            } else {
              s3 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c23); }
            }
            if (s3 === peg$FAILED) {
              if (input.charCodeAt(peg$currPos) === 44) {
                s3 = peg$c24;
                peg$currPos++;
              } else {
                s3 = peg$FAILED;
                if (peg$silentFails === 0) { peg$fail(peg$c25); }
              }
            }
            if (s3 !== peg$FAILED) {
              s4 = peg$parse_();
              if (s4 !== peg$FAILED) {
                s5 = peg$parseSelectors();
                if (s5 !== peg$FAILED) {
                  peg$savedPos = s0;
                  s1 = peg$c26(s1, s5);
                  s0 = s1;
                } else {
                  peg$currPos = s0;
                  s0 = peg$FAILED;
                }
              } else {
                peg$currPos = s0;
                s0 = peg$FAILED;
              }
            } else {
              peg$currPos = s0;
              s0 = peg$FAILED;
            }
          } else {
            peg$currPos = s0;
            s0 = peg$FAILED;
          }
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
        if (s0 === peg$FAILED) {
          s0 = peg$currPos;
          s1 = peg$parseSelector();
          if (s1 !== peg$FAILED) {
            peg$savedPos = s0;
            s1 = peg$c27(s1);
          }
          s0 = s1;
        }
      }

      return s0;
    }

    function peg$parseFilter() {
      var s0, s1, s2, s3, s4, s5, s6;

      s0 = peg$currPos;
      s1 = peg$parsePredicates();
      if (s1 !== peg$FAILED) {
        s2 = peg$parse_();
        if (s2 !== peg$FAILED) {
          if (input.charCodeAt(peg$currPos) === 42) {
            s3 = peg$c28;
            peg$currPos++;
          } else {
            s3 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c29); }
          }
          if (s3 === peg$FAILED) {
            if (input.charCodeAt(peg$currPos) === 120) {
              s3 = peg$c30;
              peg$currPos++;
            } else {
              s3 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c31); }
            }
          }
          if (s3 !== peg$FAILED) {
            s4 = peg$parse_();
            if (s4 !== peg$FAILED) {
              s5 = peg$parseInteger();
              if (s5 !== peg$FAILED) {
                peg$savedPos = s0;
                s1 = peg$c32(s1, s5);
                s0 = s1;
              } else {
                peg$currPos = s0;
                s0 = peg$FAILED;
              }
            } else {
              peg$currPos = s0;
              s0 = peg$FAILED;
            }
          } else {
            peg$currPos = s0;
            s0 = peg$FAILED;
          }
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
      if (s0 === peg$FAILED) {
        s0 = peg$currPos;
        s1 = peg$parsePredicates();
        if (s1 !== peg$FAILED) {
          s2 = peg$parse_();
          if (s2 !== peg$FAILED) {
            if (input.charCodeAt(peg$currPos) === 42) {
              s3 = peg$c28;
              peg$currPos++;
            } else {
              s3 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c29); }
            }
            if (s3 === peg$FAILED) {
              if (input.charCodeAt(peg$currPos) === 120) {
                s3 = peg$c30;
                peg$currPos++;
              } else {
                s3 = peg$FAILED;
                if (peg$silentFails === 0) { peg$fail(peg$c31); }
              }
            }
            if (s3 !== peg$FAILED) {
              s4 = peg$parse_();
              if (s4 !== peg$FAILED) {
                if (input.charCodeAt(peg$currPos) === 45) {
                  s5 = peg$c33;
                  peg$currPos++;
                } else {
                  s5 = peg$FAILED;
                  if (peg$silentFails === 0) { peg$fail(peg$c34); }
                }
                if (s5 !== peg$FAILED) {
                  s6 = peg$parseInteger();
                  if (s6 !== peg$FAILED) {
                    peg$savedPos = s0;
                    s1 = peg$c35(s1, s6);
                    s0 = s1;
                  } else {
                    peg$currPos = s0;
                    s0 = peg$FAILED;
                  }
                } else {
                  peg$currPos = s0;
                  s0 = peg$FAILED;
                }
              } else {
                peg$currPos = s0;
                s0 = peg$FAILED;
              }
            } else {
              peg$currPos = s0;
              s0 = peg$FAILED;
            }
          } else {
            peg$currPos = s0;
            s0 = peg$FAILED;
          }
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
        if (s0 === peg$FAILED) {
          s0 = peg$currPos;
          s1 = peg$parsePredicates();
          if (s1 !== peg$FAILED) {
            s2 = peg$parse_();
            if (s2 !== peg$FAILED) {
              if (input.charCodeAt(peg$currPos) === 42) {
                s3 = peg$c28;
                peg$currPos++;
              } else {
                s3 = peg$FAILED;
                if (peg$silentFails === 0) { peg$fail(peg$c29); }
              }
              if (s3 === peg$FAILED) {
                if (input.charCodeAt(peg$currPos) === 120) {
                  s3 = peg$c30;
                  peg$currPos++;
                } else {
                  s3 = peg$FAILED;
                  if (peg$silentFails === 0) { peg$fail(peg$c31); }
                }
              }
              if (s3 !== peg$FAILED) {
                s4 = peg$parse_();
                if (s4 !== peg$FAILED) {
                  if (input.substr(peg$currPos, 4) === peg$c36) {
                    s5 = peg$c36;
                    peg$currPos += 4;
                  } else {
                    s5 = peg$FAILED;
                    if (peg$silentFails === 0) { peg$fail(peg$c37); }
                  }
                  if (s5 !== peg$FAILED) {
                    peg$savedPos = s0;
                    s1 = peg$c38(s1);
                    s0 = s1;
                  } else {
                    peg$currPos = s0;
                    s0 = peg$FAILED;
                  }
                } else {
                  peg$currPos = s0;
                  s0 = peg$FAILED;
                }
              } else {
                peg$currPos = s0;
                s0 = peg$FAILED;
              }
            } else {
              peg$currPos = s0;
              s0 = peg$FAILED;
            }
          } else {
            peg$currPos = s0;
            s0 = peg$FAILED;
          }
          if (s0 === peg$FAILED) {
            s0 = peg$currPos;
            s1 = peg$parsePredicates();
            if (s1 !== peg$FAILED) {
              s2 = peg$parse_();
              if (s2 !== peg$FAILED) {
                if (input.charCodeAt(peg$currPos) === 42) {
                  s3 = peg$c28;
                  peg$currPos++;
                } else {
                  s3 = peg$FAILED;
                  if (peg$silentFails === 0) { peg$fail(peg$c29); }
                }
                if (s3 === peg$FAILED) {
                  if (input.charCodeAt(peg$currPos) === 120) {
                    s3 = peg$c30;
                    peg$currPos++;
                  } else {
                    s3 = peg$FAILED;
                    if (peg$silentFails === 0) { peg$fail(peg$c31); }
                  }
                }
                if (s3 !== peg$FAILED) {
                  s4 = peg$parse_();
                  if (s4 !== peg$FAILED) {
                    if (input.substr(peg$currPos, 3) === peg$c39) {
                      s5 = peg$c39;
                      peg$currPos += 3;
                    } else {
                      s5 = peg$FAILED;
                      if (peg$silentFails === 0) { peg$fail(peg$c40); }
                    }
                    if (s5 !== peg$FAILED) {
                      peg$savedPos = s0;
                      s1 = peg$c41(s1);
                      s0 = s1;
                    } else {
                      peg$currPos = s0;
                      s0 = peg$FAILED;
                    }
                  } else {
                    peg$currPos = s0;
                    s0 = peg$FAILED;
                  }
                } else {
                  peg$currPos = s0;
                  s0 = peg$FAILED;
                }
              } else {
                peg$currPos = s0;
                s0 = peg$FAILED;
              }
            } else {
              peg$currPos = s0;
              s0 = peg$FAILED;
            }
            if (s0 === peg$FAILED) {
              s0 = peg$currPos;
              s1 = peg$parsePredicates();
              if (s1 !== peg$FAILED) {
                s2 = peg$parse_();
                if (s2 !== peg$FAILED) {
                  if (input.charCodeAt(peg$currPos) === 42) {
                    s3 = peg$c28;
                    peg$currPos++;
                  } else {
                    s3 = peg$FAILED;
                    if (peg$silentFails === 0) { peg$fail(peg$c29); }
                  }
                  if (s3 === peg$FAILED) {
                    if (input.charCodeAt(peg$currPos) === 120) {
                      s3 = peg$c30;
                      peg$currPos++;
                    } else {
                      s3 = peg$FAILED;
                      if (peg$silentFails === 0) { peg$fail(peg$c31); }
                    }
                  }
                  if (s3 !== peg$FAILED) {
                    s4 = peg$parse_();
                    if (s4 !== peg$FAILED) {
                      if (input.substr(peg$currPos, 4) === peg$c42) {
                        s5 = peg$c42;
                        peg$currPos += 4;
                      } else {
                        s5 = peg$FAILED;
                        if (peg$silentFails === 0) { peg$fail(peg$c43); }
                      }
                      if (s5 !== peg$FAILED) {
                        peg$savedPos = s0;
                        s1 = peg$c44(s1);
                        s0 = s1;
                      } else {
                        peg$currPos = s0;
                        s0 = peg$FAILED;
                      }
                    } else {
                      peg$currPos = s0;
                      s0 = peg$FAILED;
                    }
                  } else {
                    peg$currPos = s0;
                    s0 = peg$FAILED;
                  }
                } else {
                  peg$currPos = s0;
                  s0 = peg$FAILED;
                }
              } else {
                peg$currPos = s0;
                s0 = peg$FAILED;
              }
              if (s0 === peg$FAILED) {
                s0 = peg$currPos;
                s1 = peg$parsePredicates();
                if (s1 !== peg$FAILED) {
                  peg$savedPos = s0;
                  s1 = peg$c45(s1);
                }
                s0 = s1;
              }
            }
          }
        }
      }

      return s0;
    }

    function peg$parsePredicates() {
      var s0, s1, s2, s3, s4, s5;

      if (input.substr(peg$currPos, 7) === peg$c46) {
        s0 = peg$c46;
        peg$currPos += 7;
      } else {
        s0 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c47); }
      }
      if (s0 === peg$FAILED) {
        s0 = peg$currPos;
        s1 = peg$parsePredicate();
        if (s1 !== peg$FAILED) {
          s2 = peg$parse_();
          if (s2 !== peg$FAILED) {
            if (input.substr(peg$currPos, 3) === peg$c48) {
              s3 = peg$c48;
              peg$currPos += 3;
            } else {
              s3 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c49); }
            }
            if (s3 === peg$FAILED) {
              if (input.charCodeAt(peg$currPos) === 38) {
                s3 = peg$c50;
                peg$currPos++;
              } else {
                s3 = peg$FAILED;
                if (peg$silentFails === 0) { peg$fail(peg$c51); }
              }
            }
            if (s3 !== peg$FAILED) {
              s4 = peg$parse_();
              if (s4 !== peg$FAILED) {
                s5 = peg$parsePredicates();
                if (s5 !== peg$FAILED) {
                  peg$savedPos = s0;
                  s1 = peg$c52(s1, s5);
                  s0 = s1;
                } else {
                  peg$currPos = s0;
                  s0 = peg$FAILED;
                }
              } else {
                peg$currPos = s0;
                s0 = peg$FAILED;
              }
            } else {
              peg$currPos = s0;
              s0 = peg$FAILED;
            }
          } else {
            peg$currPos = s0;
            s0 = peg$FAILED;
          }
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
        if (s0 === peg$FAILED) {
          s0 = peg$currPos;
          s1 = peg$parsePredicate();
          if (s1 !== peg$FAILED) {
            peg$savedPos = s0;
            s1 = peg$c53(s1);
          }
          s0 = s1;
        }
      }

      return s0;
    }

    function peg$parsePredicate() {
      var s0, s1, s2, s3, s4, s5;

      s0 = peg$currPos;
      if (input.substr(peg$currPos, 4) === peg$c54) {
        s1 = peg$c54;
        peg$currPos += 4;
      } else {
        s1 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c55); }
      }
      if (s1 !== peg$FAILED) {
        s2 = peg$parse_();
        if (s2 !== peg$FAILED) {
          s3 = peg$parseMode();
          if (s3 !== peg$FAILED) {
            s4 = peg$parse_();
            if (s4 !== peg$FAILED) {
              s5 = peg$parseStringLiteral();
              if (s5 !== peg$FAILED) {
                peg$savedPos = s0;
                s1 = peg$c56(s3, s5);
                s0 = s1;
              } else {
                peg$currPos = s0;
                s0 = peg$FAILED;
              }
            } else {
              peg$currPos = s0;
              s0 = peg$FAILED;
            }
          } else {
            peg$currPos = s0;
            s0 = peg$FAILED;
          }
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
      if (s0 === peg$FAILED) {
        s0 = peg$currPos;
        if (input.substr(peg$currPos, 4) === peg$c57) {
          s1 = peg$c57;
          peg$currPos += 4;
        } else {
          s1 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c58); }
        }
        if (s1 !== peg$FAILED) {
          s2 = peg$parse_();
          if (s2 !== peg$FAILED) {
            if (input.substr(peg$currPos, 2) === peg$c59) {
              s3 = peg$c59;
              peg$currPos += 2;
            } else {
              s3 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c60); }
            }
            if (s3 !== peg$FAILED) {
              s4 = peg$parse_();
              if (s4 !== peg$FAILED) {
                s5 = peg$parseType();
                if (s5 !== peg$FAILED) {
                  peg$savedPos = s0;
                  s1 = peg$c61(s5);
                  s0 = s1;
                } else {
                  peg$currPos = s0;
                  s0 = peg$FAILED;
                }
              } else {
                peg$currPos = s0;
                s0 = peg$FAILED;
              }
            } else {
              peg$currPos = s0;
              s0 = peg$FAILED;
            }
          } else {
            peg$currPos = s0;
            s0 = peg$FAILED;
          }
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
        if (s0 === peg$FAILED) {
          s0 = peg$currPos;
          s1 = peg$parseStringLiteral();
          if (s1 !== peg$FAILED) {
            peg$savedPos = s0;
            s1 = peg$c62(s1);
          }
          s0 = s1;
          if (s0 === peg$FAILED) {
            s0 = peg$currPos;
            s1 = peg$parseType();
            if (s1 !== peg$FAILED) {
              peg$savedPos = s0;
              s1 = peg$c61(s1);
            }
            s0 = s1;
          }
        }
      }

      return s0;
    }

    function peg$parseMode() {
      var s0;

      if (input.substr(peg$currPos, 2) === peg$c59) {
        s0 = peg$c59;
        peg$currPos += 2;
      } else {
        s0 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c60); }
      }
      if (s0 === peg$FAILED) {
        if (input.substr(peg$currPos, 2) === peg$c63) {
          s0 = peg$c63;
          peg$currPos += 2;
        } else {
          s0 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c64); }
        }
        if (s0 === peg$FAILED) {
          if (input.substr(peg$currPos, 10) === peg$c65) {
            s0 = peg$c65;
            peg$currPos += 10;
          } else {
            s0 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c66); }
          }
          if (s0 === peg$FAILED) {
            if (input.substr(peg$currPos, 8) === peg$c67) {
              s0 = peg$c67;
              peg$currPos += 8;
            } else {
              s0 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c68); }
            }
            if (s0 === peg$FAILED) {
              if (input.substr(peg$currPos, 2) === peg$c69) {
                s0 = peg$c69;
                peg$currPos += 2;
              } else {
                s0 = peg$FAILED;
                if (peg$silentFails === 0) { peg$fail(peg$c70); }
              }
              if (s0 === peg$FAILED) {
                if (input.substr(peg$currPos, 2) === peg$c71) {
                  s0 = peg$c71;
                  peg$currPos += 2;
                } else {
                  s0 = peg$FAILED;
                  if (peg$silentFails === 0) { peg$fail(peg$c72); }
                }
                if (s0 === peg$FAILED) {
                  if (input.charCodeAt(peg$currPos) === 62) {
                    s0 = peg$c73;
                    peg$currPos++;
                  } else {
                    s0 = peg$FAILED;
                    if (peg$silentFails === 0) { peg$fail(peg$c74); }
                  }
                  if (s0 === peg$FAILED) {
                    if (input.charCodeAt(peg$currPos) === 60) {
                      s0 = peg$c75;
                      peg$currPos++;
                    } else {
                      s0 = peg$FAILED;
                      if (peg$silentFails === 0) { peg$fail(peg$c76); }
                    }
                  }
                }
              }
            }
          }
        }
      }

      return s0;
    }

    function peg$parseType() {
      var s0;

      if (input.substr(peg$currPos, 11) === peg$c77) {
        s0 = peg$c77;
        peg$currPos += 11;
      } else {
        s0 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c78); }
      }
      if (s0 === peg$FAILED) {
        if (input.substr(peg$currPos, 6) === peg$c79) {
          s0 = peg$c79;
          peg$currPos += 6;
        } else {
          s0 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c80); }
        }
        if (s0 === peg$FAILED) {
          if (input.substr(peg$currPos, 5) === peg$c81) {
            s0 = peg$c81;
            peg$currPos += 5;
          } else {
            s0 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c82); }
          }
          if (s0 === peg$FAILED) {
            if (input.substr(peg$currPos, 7) === peg$c83) {
              s0 = peg$c83;
              peg$currPos += 7;
            } else {
              s0 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c84); }
            }
            if (s0 === peg$FAILED) {
              if (input.substr(peg$currPos, 10) === peg$c85) {
                s0 = peg$c85;
                peg$currPos += 10;
              } else {
                s0 = peg$FAILED;
                if (peg$silentFails === 0) { peg$fail(peg$c86); }
              }
              if (s0 === peg$FAILED) {
                if (input.substr(peg$currPos, 3) === peg$c87) {
                  s0 = peg$c87;
                  peg$currPos += 3;
                } else {
                  s0 = peg$FAILED;
                  if (peg$silentFails === 0) { peg$fail(peg$c88); }
                }
                if (s0 === peg$FAILED) {
                  if (input.substr(peg$currPos, 5) === peg$c89) {
                    s0 = peg$c89;
                    peg$currPos += 5;
                  } else {
                    s0 = peg$FAILED;
                    if (peg$silentFails === 0) { peg$fail(peg$c90); }
                  }
                  if (s0 === peg$FAILED) {
                    if (input.substr(peg$currPos, 4) === peg$c91) {
                      s0 = peg$c91;
                      peg$currPos += 4;
                    } else {
                      s0 = peg$FAILED;
                      if (peg$silentFails === 0) { peg$fail(peg$c92); }
                    }
                    if (s0 === peg$FAILED) {
                      if (input.substr(peg$currPos, 4) === peg$c93) {
                        s0 = peg$c93;
                        peg$currPos += 4;
                      } else {
                        s0 = peg$FAILED;
                        if (peg$silentFails === 0) { peg$fail(peg$c94); }
                      }
                      if (s0 === peg$FAILED) {
                        if (input.substr(peg$currPos, 4) === peg$c95) {
                          s0 = peg$c95;
                          peg$currPos += 4;
                        } else {
                          s0 = peg$FAILED;
                          if (peg$silentFails === 0) { peg$fail(peg$c96); }
                        }
                        if (s0 === peg$FAILED) {
                          if (input.substr(peg$currPos, 4) === peg$c97) {
                            s0 = peg$c97;
                            peg$currPos += 4;
                          } else {
                            s0 = peg$FAILED;
                            if (peg$silentFails === 0) { peg$fail(peg$c98); }
                          }
                          if (s0 === peg$FAILED) {
                            if (input.substr(peg$currPos, 4) === peg$c99) {
                              s0 = peg$c99;
                              peg$currPos += 4;
                            } else {
                              s0 = peg$FAILED;
                              if (peg$silentFails === 0) { peg$fail(peg$c100); }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }

      return s0;
    }

    function peg$parseReserved() {
      var s0;

      if (input.charCodeAt(peg$currPos) === 59) {
        s0 = peg$c2;
        peg$currPos++;
      } else {
        s0 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c3); }
      }
      if (s0 === peg$FAILED) {
        if (input.charCodeAt(peg$currPos) === 61) {
          s0 = peg$c6;
          peg$currPos++;
        } else {
          s0 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c7); }
        }
        if (s0 === peg$FAILED) {
          if (input.substr(peg$currPos, 7) === peg$c9) {
            s0 = peg$c9;
            peg$currPos += 7;
          } else {
            s0 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c10); }
          }
          if (s0 === peg$FAILED) {
            if (input.charCodeAt(peg$currPos) === 91) {
              s0 = peg$c14;
              peg$currPos++;
            } else {
              s0 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c15); }
            }
            if (s0 === peg$FAILED) {
              if (input.charCodeAt(peg$currPos) === 93) {
                s0 = peg$c16;
                peg$currPos++;
              } else {
                s0 = peg$FAILED;
                if (peg$silentFails === 0) { peg$fail(peg$c17); }
              }
              if (s0 === peg$FAILED) {
                if (input.substr(peg$currPos, 2) === peg$c22) {
                  s0 = peg$c22;
                  peg$currPos += 2;
                } else {
                  s0 = peg$FAILED;
                  if (peg$silentFails === 0) { peg$fail(peg$c23); }
                }
                if (s0 === peg$FAILED) {
                  if (input.charCodeAt(peg$currPos) === 44) {
                    s0 = peg$c24;
                    peg$currPos++;
                  } else {
                    s0 = peg$FAILED;
                    if (peg$silentFails === 0) { peg$fail(peg$c25); }
                  }
                  if (s0 === peg$FAILED) {
                    if (input.substr(peg$currPos, 10) === peg$c19) {
                      s0 = peg$c19;
                      peg$currPos += 10;
                    } else {
                      s0 = peg$FAILED;
                      if (peg$silentFails === 0) { peg$fail(peg$c20); }
                    }
                    if (s0 === peg$FAILED) {
                      if (input.charCodeAt(peg$currPos) === 42) {
                        s0 = peg$c28;
                        peg$currPos++;
                      } else {
                        s0 = peg$FAILED;
                        if (peg$silentFails === 0) { peg$fail(peg$c29); }
                      }
                      if (s0 === peg$FAILED) {
                        if (input.charCodeAt(peg$currPos) === 120) {
                          s0 = peg$c30;
                          peg$currPos++;
                        } else {
                          s0 = peg$FAILED;
                          if (peg$silentFails === 0) { peg$fail(peg$c31); }
                        }
                        if (s0 === peg$FAILED) {
                          if (input.substr(peg$currPos, 3) === peg$c39) {
                            s0 = peg$c39;
                            peg$currPos += 3;
                          } else {
                            s0 = peg$FAILED;
                            if (peg$silentFails === 0) { peg$fail(peg$c40); }
                          }
                          if (s0 === peg$FAILED) {
                            if (input.substr(peg$currPos, 4) === peg$c36) {
                              s0 = peg$c36;
                              peg$currPos += 4;
                            } else {
                              s0 = peg$FAILED;
                              if (peg$silentFails === 0) { peg$fail(peg$c37); }
                            }
                            if (s0 === peg$FAILED) {
                              if (input.charCodeAt(peg$currPos) === 45) {
                                s0 = peg$c33;
                                peg$currPos++;
                              } else {
                                s0 = peg$FAILED;
                                if (peg$silentFails === 0) { peg$fail(peg$c34); }
                              }
                              if (s0 === peg$FAILED) {
                                if (input.substr(peg$currPos, 7) === peg$c46) {
                                  s0 = peg$c46;
                                  peg$currPos += 7;
                                } else {
                                  s0 = peg$FAILED;
                                  if (peg$silentFails === 0) { peg$fail(peg$c47); }
                                }
                                if (s0 === peg$FAILED) {
                                  if (input.substr(peg$currPos, 3) === peg$c48) {
                                    s0 = peg$c48;
                                    peg$currPos += 3;
                                  } else {
                                    s0 = peg$FAILED;
                                    if (peg$silentFails === 0) { peg$fail(peg$c49); }
                                  }
                                  if (s0 === peg$FAILED) {
                                    if (input.charCodeAt(peg$currPos) === 38) {
                                      s0 = peg$c50;
                                      peg$currPos++;
                                    } else {
                                      s0 = peg$FAILED;
                                      if (peg$silentFails === 0) { peg$fail(peg$c51); }
                                    }
                                    if (s0 === peg$FAILED) {
                                      s0 = peg$parseType();
                                      if (s0 === peg$FAILED) {
                                        s0 = peg$parseMode();
                                        if (s0 === peg$FAILED) {
                                          if (input.substr(peg$currPos, 4) === peg$c54) {
                                            s0 = peg$c54;
                                            peg$currPos += 4;
                                          } else {
                                            s0 = peg$FAILED;
                                            if (peg$silentFails === 0) { peg$fail(peg$c55); }
                                          }
                                          if (s0 === peg$FAILED) {
                                            if (input.substr(peg$currPos, 4) === peg$c57) {
                                              s0 = peg$c57;
                                              peg$currPos += 4;
                                            } else {
                                              s0 = peg$FAILED;
                                              if (peg$silentFails === 0) { peg$fail(peg$c58); }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }

      return s0;
    }

    function peg$parseName() {
      var s0, s1, s2, s3, s4;

      s0 = peg$currPos;
      s1 = peg$currPos;
      peg$silentFails++;
      s2 = peg$parseReserved();
      peg$silentFails--;
      if (s2 === peg$FAILED) {
        s1 = void 0;
      } else {
        peg$currPos = s1;
        s1 = peg$FAILED;
      }
      if (s1 !== peg$FAILED) {
        if (peg$c101.test(input.charAt(peg$currPos))) {
          s2 = input.charAt(peg$currPos);
          peg$currPos++;
        } else {
          s2 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c102); }
        }
        if (s2 !== peg$FAILED) {
          s3 = [];
          if (peg$c103.test(input.charAt(peg$currPos))) {
            s4 = input.charAt(peg$currPos);
            peg$currPos++;
          } else {
            s4 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c104); }
          }
          while (s4 !== peg$FAILED) {
            s3.push(s4);
            if (peg$c103.test(input.charAt(peg$currPos))) {
              s4 = input.charAt(peg$currPos);
              peg$currPos++;
            } else {
              s4 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c104); }
            }
          }
          if (s3 !== peg$FAILED) {
            peg$savedPos = s0;
            s1 = peg$c105(s2, s3);
            s0 = s1;
          } else {
            peg$currPos = s0;
            s0 = peg$FAILED;
          }
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }

      return s0;
    }

    function peg$parseInteger() {
      var s0, s1, s2, s3, s4;

      s0 = peg$currPos;
      s1 = peg$currPos;
      if (peg$c106.test(input.charAt(peg$currPos))) {
        s2 = input.charAt(peg$currPos);
        peg$currPos++;
      } else {
        s2 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c107); }
      }
      if (s2 !== peg$FAILED) {
        s3 = [];
        if (peg$c108.test(input.charAt(peg$currPos))) {
          s4 = input.charAt(peg$currPos);
          peg$currPos++;
        } else {
          s4 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c109); }
        }
        while (s4 !== peg$FAILED) {
          s3.push(s4);
          if (peg$c108.test(input.charAt(peg$currPos))) {
            s4 = input.charAt(peg$currPos);
            peg$currPos++;
          } else {
            s4 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c109); }
          }
        }
        if (s3 !== peg$FAILED) {
          s2 = [s2, s3];
          s1 = s2;
        } else {
          peg$currPos = s1;
          s1 = peg$FAILED;
        }
      } else {
        peg$currPos = s1;
        s1 = peg$FAILED;
      }
      if (s1 !== peg$FAILED) {
        peg$savedPos = s0;
        s1 = peg$c110(s1);
      }
      s0 = s1;

      return s0;
    }

    function peg$parse_() {
      var s0, s1;

      s0 = [];
      if (peg$c111.test(input.charAt(peg$currPos))) {
        s1 = input.charAt(peg$currPos);
        peg$currPos++;
      } else {
        s1 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c112); }
      }
      while (s1 !== peg$FAILED) {
        s0.push(s1);
        if (peg$c111.test(input.charAt(peg$currPos))) {
          s1 = input.charAt(peg$currPos);
          peg$currPos++;
        } else {
          s1 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c112); }
        }
      }

      return s0;
    }

    function peg$parseStringLiteral() {
      var s0, s1, s2, s3;

      s0 = peg$currPos;
      if (peg$c113.test(input.charAt(peg$currPos))) {
        s1 = input.charAt(peg$currPos);
        peg$currPos++;
      } else {
        s1 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c114); }
      }
      if (s1 !== peg$FAILED) {
        s2 = [];
        if (peg$c115.test(input.charAt(peg$currPos))) {
          s3 = input.charAt(peg$currPos);
          peg$currPos++;
        } else {
          s3 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c116); }
        }
        if (s3 !== peg$FAILED) {
          while (s3 !== peg$FAILED) {
            s2.push(s3);
            if (peg$c115.test(input.charAt(peg$currPos))) {
              s3 = input.charAt(peg$currPos);
              peg$currPos++;
            } else {
              s3 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c116); }
            }
          }
        } else {
          s2 = peg$FAILED;
        }
        if (s2 !== peg$FAILED) {
          if (peg$c113.test(input.charAt(peg$currPos))) {
            s3 = input.charAt(peg$currPos);
            peg$currPos++;
          } else {
            s3 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c114); }
          }
          if (s3 !== peg$FAILED) {
            peg$savedPos = s0;
            s1 = peg$c117(s2);
            s0 = s1;
          } else {
            peg$currPos = s0;
            s0 = peg$FAILED;
          }
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }

      return s0;
    }


    var cons = function (e) {
      return function (es) {
        return [e].concat(es);
      };
    };

    function unconss(empty,next,xs){
          return xs.length === 0 ? empty : next(xs[0])(xs.slice(1));
     };

    // ----------------------------------------------------------------
    var All = (function () {
        function All(all) {
            this.all = all;
        };
        All.create = function (all) {
            return new All(all);
        };
        return All;
    })();
    var NAll = (function () {
        function NAll(nall) {
            this.nall = nall;
        };
        NAll.create = function (nall) {
            return new NAll(nall);
        };
        return NAll;
    })();
    var Exact = (function () {
        function Exact(exact) {
            this.exact = exact;
        };
        Exact.create = function (exact) {
            return new Exact(exact);
        };
        return Exact;
    })();
    var Equal = (function () {
        function Equal() {

        };
        Equal.value = new Equal();
        return Equal;
    })();
    var StartsWith = (function () {
        function StartsWith() {

        };
        StartsWith.value = new StartsWith();
        return StartsWith;
    })();
    var Contains = (function () {
        function Contains() {

        };
        Contains.value = new Contains();
        return Contains;
    })();
    var Greater = (function () {
        function Greater() {

        };
        Greater.value = new Greater();
        return Greater;
    })();
    var Less = (function () {
        function Less() {

        };
        Less.value = new Less();
        return Less;
    })();
    var GreaterEqual = (function () {
        function GreaterEqual() {

        };
        GreaterEqual.value = new GreaterEqual();
        return GreaterEqual;
    })();
    var LessEqual = (function () {
        function LessEqual() {

        };
        LessEqual.value = new LessEqual();
        return LessEqual;
    })();
    var Negative = (function () {
        function Negative(negative) {
            this.negative = negative;
        };
        Negative.create = function (negative) {
            return new Negative(negative);
        };
        return Negative;
    })();
    var Positive = (function () {
        function Positive(positive) {
            this.positive = positive;
        };
        Positive.create = function (positive) {
            return new Positive(positive);
        };
        return Positive;
    })();
    var Direct = (function () {
        function Direct(direct) {
            this.direct = direct;
        };
        Direct.create = function (direct) {
            return new Direct(direct);
        };
        return Direct;
    })();
    var Exclude = (function () {
        function Exclude(exclude) {
            this.exclude = exclude;
        };
        Exclude.create = function (exclude) {
            return new Exclude(exclude);
        };
        return Exclude;
    })();
    var Sequence = (function () {
        function Sequence(sequence) {
            this.sequence = sequence;
        };
        Sequence.create = function (sequence) {
            return new Sequence(sequence);
        };
        return Sequence;
    })();
    var Var = (function () {
        function Var(variable) {
            this.variable = variable;
        };
        Var.create = function (variable) {
            return new Var(variable);
        };
        return Var;
    })();

    // ----------------------------------------------------------------

    var lookUpDefinition = function (c) {
        return function (selectorName) {
            return unconss
                     ( new Direct({
                predicates: [  ],
                quantity: new Exact(0)
            })
                     , function (d) {
                		 return function (ds) {
                    	 	var $7 = d.name === selectorName;
                            if ($7) {
                        		return d.selector;
                            };
                    	    return lookUpDefinition(ds)(selectorName);
                	   }}
                     , c);
        };
    };

    // ----------------------------------------------------------------

    var flatten = function (c) {
        return function (v) {
            if (v instanceof Direct) {
                return [ v.direct ];
            };
            if (v instanceof Sequence) {
                return v.sequence.flatMap(flatten(c));
            };
            if (v instanceof Var) {
                return flatten(c)(lookUpDefinition(c)(v.variable));
            };
    		if (v instanceof Exclude && (v.exclude instanceof Direct && v.exclude.direct.quantity instanceof Exact)) {
                if (v.exclude.direct.quantity.exact >= 0) {
                    return [ {
                        predicates: v.exclude.direct.predicates,
                        quantity:   new Exact(-v.exclude.direct.quantity.exact)
                    } ];
                } else {
                    return [ {
                        predicates: v.exclude.direct.predicates,
                        quantity: new Exact(v.exclude.direct.quantity.exact)
                    } ];
                };
            };
            if (v instanceof Exclude && (v.exclude instanceof Direct && v.exclude.direct.quantity instanceof All)) {
                return [ {
                   predicates: v.exclude.direct.predicates,
                   quantity: new NAll(null)
                } ];
            };
            if (v instanceof Exclude && (v.exclude instanceof Direct && v.exclude.direct.quantity instanceof NAll)) {
                return [ {
                   predicates: v.exclude.direct.predicates,
                   quantity: new Nall(null)
                } ];
            };
            if (v instanceof Exclude && v.exclude instanceof Exclude) {
                return flatten(c)(new Exclude(v.exclude.exclude));
            };
            if (v instanceof Exclude && v.exclude instanceof Sequence) {
                return flatten(c)(new Sequence(v.exclude.sequence.map(s => new Exclude(s))));
            };
            if (v instanceof Exclude && v.exclude instanceof Var) {
                return flatten(c)(new Exclude(lookUpDefinition(c)(v.exclude.variable)));
            };
            console.log(v);
            throw new Error("Failed pattern match at Main (line 66, column 1 - line 66, column 46): " + [ c.constructor.name, v.constructor.name ]);
        };
    };

    // ----------------------------------------------------------------

    function flattenAll(c) {
        var r = c.map(d => ({ "name": d.name , "selectors": (flatten(c)(d.selector))}) );
        return r;
    };

    // ----------------------------------------------------------------
    function checkVars (n, names, o) {
        var error = null;
        if (o.exclude != null) {
           error = checkVars (n , names, o.exclude);
        } else if (o.selectors != null) {
          for (var k = 0; k < o.selectors.length; k++) {
             error = checkVars (n , names, o.selectors[k]);
             if (error !=null) {
               break;
             }
          }
        } else if (o.variable != null) {
          if (names.indexOf(o.variable) < 0) {
            error = o.variable;
          }
        } else {
          error = null;
        }
        return error;
      }
    // ----------------------------------------------------------------


    peg$result = peg$startRuleFunction();

    if (peg$result !== peg$FAILED && peg$currPos === input.length) {
      return peg$result;
    } else {
      if (peg$result !== peg$FAILED && peg$currPos < input.length) {
        peg$fail(peg$endExpectation());
      }

      throw peg$buildStructuredError(
        peg$maxFailExpected,
        peg$maxFailPos < input.length ? input.charAt(peg$maxFailPos) : null,
        peg$maxFailPos < input.length
          ? peg$computeLocation(peg$maxFailPos, peg$maxFailPos + 1)
          : peg$computeLocation(peg$maxFailPos, peg$maxFailPos)
      );
    }
  }

  return {
    SyntaxError: peg$SyntaxError,
    parse:       peg$parse
  };
})();
