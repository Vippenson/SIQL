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

        peg$startRuleFunctions = { Config: peg$parseConfig },
        peg$startRuleFunction  = peg$parseConfig,

        peg$c0 = ";",
        peg$c1 = peg$literalExpectation(";", false),
        peg$c2 = function(d, c) { c.unshift(d);
              return c},
        peg$c3 = function(d) {return [ d ]},
        peg$c4 = ":=",
        peg$c5 = peg$literalExpectation(":=", false),
        peg$c6 = function(n, s) {return {"name": n, "selector": s}},
        peg$c7 = "except",
        peg$c8 = peg$literalExpectation("except", false),
        peg$c9 = function(n) {return {"except": n}},
        peg$c10 = "also",
        peg$c11 = peg$literalExpectation("also", false),
        peg$c12 = function(n, ns) { ns.unshift(n);
             return ns },
        peg$c13 = function(n) {return [ n ]},
        peg$c14 = "or",
        peg$c15 = peg$literalExpectation("or", false),
        peg$c16 = function(f, fs) {fs.unshift(f);
             return fs},
        peg$c17 = function(f) {return [ f ]},
        peg$c18 = "*",
        peg$c19 = peg$literalExpectation("*", false),
        peg$c20 = function(ps, q) {return {"predicates":ps, "quantities":q}},
        peg$c21 = "(",
        peg$c22 = peg$literalExpectation("(", false),
        peg$c23 = ")",
        peg$c24 = peg$literalExpectation(")", false),
        peg$c25 = function(ps) {return ps},
        peg$c26 = "and",
        peg$c27 = peg$literalExpectation("and", false),
        peg$c28 = function(p, ps) {ps.unshift(p);
           return ps},
        peg$c29 = function(p) {return [p]},
        peg$c30 = function(p) {return p},
        peg$c31 = "name",
        peg$c32 = peg$literalExpectation("name", false),
        peg$c33 = function(m, s) {return {"name": s, "Mode": m}},
        peg$c34 = "type",
        peg$c35 = peg$literalExpectation("type", false),
        peg$c36 = "is",
        peg$c37 = peg$literalExpectation("is", false),
        peg$c38 = function(t) {return {"type": t}},
        peg$c39 = function(s) {return {"name": s, "Mode": "is"}},
        peg$c40 = "startsWith",
        peg$c41 = peg$literalExpectation("startsWith", false),
        peg$c42 = "contains",
        peg$c43 = peg$literalExpectation("contains", false),
        peg$c44 = "WEAPON",
        peg$c45 = peg$literalExpectation("WEAPON", false),
        peg$c46 = "ARMOR",
        peg$c47 = peg$literalExpectation("ARMOR", false),
        peg$c48 = "APPAREL",
        peg$c49 = peg$literalExpectation("APPAREL", false),
        peg$c50 = "AMMO",
        peg$c51 = peg$literalExpectation("AMMO", false),
        peg$c52 = "MISC",
        peg$c53 = peg$literalExpectation("MISC", false),
        peg$c54 = /^[a-zA-Z]/,
        peg$c55 = peg$classExpectation([["a", "z"], ["A", "Z"]], false, false),
        peg$c56 = /^[a-zA-Z0-9]/,
        peg$c57 = peg$classExpectation([["a", "z"], ["A", "Z"], ["0", "9"]], false, false),
        peg$c58 = function(d, ds) { return d + ds.join('') },
        peg$c59 = /^[0-9]/,
        peg$c60 = peg$classExpectation([["0", "9"]], false, false),
        peg$c61 = function(n) {return Number(n)},
        peg$c62 = /^[ \t\n\r]/,
        peg$c63 = peg$classExpectation([" ", "\t", "\n", "\r"], false, false),
        peg$c64 = /^["]/,
        peg$c65 = peg$classExpectation(["\""], false, false),
        peg$c66 = /^[a-zA-Z0-9 ]/,
        peg$c67 = peg$classExpectation([["a", "z"], ["A", "Z"], ["0", "9"], " "], false, false),
        peg$c68 = function(s) {return s.join('')},

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

    function peg$parseConfig() {
      var s0, s1, s2, s3, s4, s5;

      s0 = peg$currPos;
      s1 = peg$parseDefinition();
      if (s1 !== peg$FAILED) {
        s2 = peg$parse_();
        if (s2 !== peg$FAILED) {
          if (input.charCodeAt(peg$currPos) === 59) {
            s3 = peg$c0;
            peg$currPos++;
          } else {
            s3 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c1); }
          }
          if (s3 !== peg$FAILED) {
            s4 = peg$parse_();
            if (s4 !== peg$FAILED) {
              s5 = peg$parseConfig();
              if (s5 !== peg$FAILED) {
                peg$savedPos = s0;
                s1 = peg$c2(s1, s5);
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
              s3 = peg$c0;
              peg$currPos++;
            } else {
              s3 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c1); }
            }
            if (s3 !== peg$FAILED) {
              s4 = peg$parse_();
              if (s4 !== peg$FAILED) {
                peg$savedPos = s0;
                s1 = peg$c3(s1);
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
          if (input.substr(peg$currPos, 2) === peg$c4) {
            s3 = peg$c4;
            peg$currPos += 2;
          } else {
            s3 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c5); }
          }
          if (s3 !== peg$FAILED) {
            s4 = peg$parse_();
            if (s4 !== peg$FAILED) {
              s5 = peg$parseSelector();
              if (s5 !== peg$FAILED) {
                peg$savedPos = s0;
                s1 = peg$c6(s1, s5);
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
      var s0, s1, s2, s3;

      s0 = peg$currPos;
      if (input.substr(peg$currPos, 6) === peg$c7) {
        s1 = peg$c7;
        peg$currPos += 6;
      } else {
        s1 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c8); }
      }
      if (s1 !== peg$FAILED) {
        s2 = peg$parse_();
        if (s2 !== peg$FAILED) {
          s3 = peg$parseName();
          if (s3 !== peg$FAILED) {
            peg$savedPos = s0;
            s1 = peg$c9(s3);
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
        s0 = peg$parseNames();
        if (s0 === peg$FAILED) {
          s0 = peg$parseFilters();
        }
      }

      return s0;
    }

    function peg$parseNames() {
      var s0, s1, s2, s3, s4, s5;

      s0 = peg$currPos;
      s1 = peg$parseName();
      if (s1 !== peg$FAILED) {
        s2 = peg$parse_();
        if (s2 !== peg$FAILED) {
          if (input.substr(peg$currPos, 4) === peg$c10) {
            s3 = peg$c10;
            peg$currPos += 4;
          } else {
            s3 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c11); }
          }
          if (s3 !== peg$FAILED) {
            s4 = peg$parse_();
            if (s4 !== peg$FAILED) {
              s5 = peg$parseNames();
              if (s5 !== peg$FAILED) {
                peg$savedPos = s0;
                s1 = peg$c12(s1, s5);
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
        s1 = peg$parseName();
        if (s1 !== peg$FAILED) {
          peg$savedPos = s0;
          s1 = peg$c13(s1);
        }
        s0 = s1;
      }

      return s0;
    }

    function peg$parseFilters() {
      var s0, s1, s2, s3, s4, s5;

      s0 = peg$currPos;
      s1 = peg$parseFilter();
      if (s1 !== peg$FAILED) {
        s2 = peg$parse_();
        if (s2 !== peg$FAILED) {
          if (input.substr(peg$currPos, 2) === peg$c14) {
            s3 = peg$c14;
            peg$currPos += 2;
          } else {
            s3 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c15); }
          }
          if (s3 !== peg$FAILED) {
            s4 = peg$parse_();
            if (s4 !== peg$FAILED) {
              s5 = peg$parseFilters();
              if (s5 !== peg$FAILED) {
                peg$savedPos = s0;
                s1 = peg$c16(s1, s5);
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
        s1 = peg$parseFilter();
        if (s1 !== peg$FAILED) {
          peg$savedPos = s0;
          s1 = peg$c17(s1);
        }
        s0 = s1;
      }

      return s0;
    }

    function peg$parseFilter() {
      var s0, s1, s2, s3, s4, s5;

      s0 = peg$currPos;
      s1 = peg$parsePredicates();
      if (s1 !== peg$FAILED) {
        s2 = peg$parse_();
        if (s2 !== peg$FAILED) {
          if (input.charCodeAt(peg$currPos) === 42) {
            s3 = peg$c18;
            peg$currPos++;
          } else {
            s3 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c19); }
          }
          if (s3 !== peg$FAILED) {
            s4 = peg$parse_();
            if (s4 !== peg$FAILED) {
              s5 = peg$parseInteger();
              if (s5 !== peg$FAILED) {
                peg$savedPos = s0;
                s1 = peg$c20(s1, s5);
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

    function peg$parsePredicates() {
      var s0, s1, s2, s3, s4, s5;

      s0 = peg$currPos;
      if (input.charCodeAt(peg$currPos) === 40) {
        s1 = peg$c21;
        peg$currPos++;
      } else {
        s1 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c22); }
      }
      if (s1 !== peg$FAILED) {
        s2 = peg$parse_();
        if (s2 !== peg$FAILED) {
          s3 = peg$parsePredicates();
          if (s3 !== peg$FAILED) {
            s4 = peg$parse_();
            if (s4 !== peg$FAILED) {
              if (input.charCodeAt(peg$currPos) === 41) {
                s5 = peg$c23;
                peg$currPos++;
              } else {
                s5 = peg$FAILED;
                if (peg$silentFails === 0) { peg$fail(peg$c24); }
              }
              if (s5 !== peg$FAILED) {
                peg$savedPos = s0;
                s1 = peg$c25(s3);
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
          s2 = peg$parse_();
          if (s2 !== peg$FAILED) {
            if (input.substr(peg$currPos, 3) === peg$c26) {
              s3 = peg$c26;
              peg$currPos += 3;
            } else {
              s3 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c27); }
            }
            if (s3 !== peg$FAILED) {
              s4 = peg$parse_();
              if (s4 !== peg$FAILED) {
                s5 = peg$parsePredicates();
                if (s5 !== peg$FAILED) {
                  peg$savedPos = s0;
                  s1 = peg$c28(s1, s5);
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
            s1 = peg$c29(s1);
          }
          s0 = s1;
        }
      }

      return s0;
    }

    function peg$parsePredicate() {
      var s0, s1, s2, s3, s4, s5;

      s0 = peg$currPos;
      if (input.charCodeAt(peg$currPos) === 40) {
        s1 = peg$c21;
        peg$currPos++;
      } else {
        s1 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c22); }
      }
      if (s1 !== peg$FAILED) {
        s2 = peg$parse_();
        if (s2 !== peg$FAILED) {
          s3 = peg$parsePredicate();
          if (s3 !== peg$FAILED) {
            s4 = peg$parse_();
            if (s4 !== peg$FAILED) {
              if (input.charCodeAt(peg$currPos) === 41) {
                s5 = peg$c23;
                peg$currPos++;
              } else {
                s5 = peg$FAILED;
                if (peg$silentFails === 0) { peg$fail(peg$c24); }
              }
              if (s5 !== peg$FAILED) {
                peg$savedPos = s0;
                s1 = peg$c30(s3);
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
        if (input.substr(peg$currPos, 4) === peg$c31) {
          s1 = peg$c31;
          peg$currPos += 4;
        } else {
          s1 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c32); }
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
                  s1 = peg$c33(s3, s5);
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
          if (input.substr(peg$currPos, 4) === peg$c34) {
            s1 = peg$c34;
            peg$currPos += 4;
          } else {
            s1 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c35); }
          }
          if (s1 !== peg$FAILED) {
            s2 = peg$parse_();
            if (s2 !== peg$FAILED) {
              if (input.substr(peg$currPos, 2) === peg$c36) {
                s3 = peg$c36;
                peg$currPos += 2;
              } else {
                s3 = peg$FAILED;
                if (peg$silentFails === 0) { peg$fail(peg$c37); }
              }
              if (s3 !== peg$FAILED) {
                s4 = peg$parse_();
                if (s4 !== peg$FAILED) {
                  s5 = peg$parseType();
                  if (s5 !== peg$FAILED) {
                    peg$savedPos = s0;
                    s1 = peg$c38(s5);
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
              s1 = peg$c39(s1);
            }
            s0 = s1;
          }
        }
      }

      return s0;
    }

    function peg$parseMode() {
      var s0;

      if (input.substr(peg$currPos, 2) === peg$c36) {
        s0 = peg$c36;
        peg$currPos += 2;
      } else {
        s0 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c37); }
      }
      if (s0 === peg$FAILED) {
        if (input.substr(peg$currPos, 10) === peg$c40) {
          s0 = peg$c40;
          peg$currPos += 10;
        } else {
          s0 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c41); }
        }
        if (s0 === peg$FAILED) {
          if (input.substr(peg$currPos, 8) === peg$c42) {
            s0 = peg$c42;
            peg$currPos += 8;
          } else {
            s0 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c43); }
          }
        }
      }

      return s0;
    }

    function peg$parseType() {
      var s0;

      if (input.substr(peg$currPos, 6) === peg$c44) {
        s0 = peg$c44;
        peg$currPos += 6;
      } else {
        s0 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c45); }
      }
      if (s0 === peg$FAILED) {
        if (input.substr(peg$currPos, 5) === peg$c46) {
          s0 = peg$c46;
          peg$currPos += 5;
        } else {
          s0 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c47); }
        }
        if (s0 === peg$FAILED) {
          if (input.substr(peg$currPos, 7) === peg$c48) {
            s0 = peg$c48;
            peg$currPos += 7;
          } else {
            s0 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c49); }
          }
          if (s0 === peg$FAILED) {
            if (input.substr(peg$currPos, 4) === peg$c50) {
              s0 = peg$c50;
              peg$currPos += 4;
            } else {
              s0 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c51); }
            }
            if (s0 === peg$FAILED) {
              if (input.substr(peg$currPos, 4) === peg$c52) {
                s0 = peg$c52;
                peg$currPos += 4;
              } else {
                s0 = peg$FAILED;
                if (peg$silentFails === 0) { peg$fail(peg$c53); }
              }
            }
          }
        }
      }

      return s0;
    }

    function peg$parseReserved() {
      var s0;

      s0 = peg$parseType();
      if (s0 === peg$FAILED) {
        s0 = peg$parseMode();
        if (s0 === peg$FAILED) {
          if (input.substr(peg$currPos, 2) === peg$c4) {
            s0 = peg$c4;
            peg$currPos += 2;
          } else {
            s0 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c5); }
          }
          if (s0 === peg$FAILED) {
            if (input.substr(peg$currPos, 2) === peg$c14) {
              s0 = peg$c14;
              peg$currPos += 2;
            } else {
              s0 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c15); }
            }
            if (s0 === peg$FAILED) {
              if (input.substr(peg$currPos, 3) === peg$c26) {
                s0 = peg$c26;
                peg$currPos += 3;
              } else {
                s0 = peg$FAILED;
                if (peg$silentFails === 0) { peg$fail(peg$c27); }
              }
              if (s0 === peg$FAILED) {
                if (input.substr(peg$currPos, 4) === peg$c10) {
                  s0 = peg$c10;
                  peg$currPos += 4;
                } else {
                  s0 = peg$FAILED;
                  if (peg$silentFails === 0) { peg$fail(peg$c11); }
                }
                if (s0 === peg$FAILED) {
                  if (input.charCodeAt(peg$currPos) === 40) {
                    s0 = peg$c21;
                    peg$currPos++;
                  } else {
                    s0 = peg$FAILED;
                    if (peg$silentFails === 0) { peg$fail(peg$c22); }
                  }
                  if (s0 === peg$FAILED) {
                    if (input.charCodeAt(peg$currPos) === 41) {
                      s0 = peg$c23;
                      peg$currPos++;
                    } else {
                      s0 = peg$FAILED;
                      if (peg$silentFails === 0) { peg$fail(peg$c24); }
                    }
                    if (s0 === peg$FAILED) {
                      if (input.substr(peg$currPos, 4) === peg$c31) {
                        s0 = peg$c31;
                        peg$currPos += 4;
                      } else {
                        s0 = peg$FAILED;
                        if (peg$silentFails === 0) { peg$fail(peg$c32); }
                      }
                      if (s0 === peg$FAILED) {
                        if (input.substr(peg$currPos, 4) === peg$c34) {
                          s0 = peg$c34;
                          peg$currPos += 4;
                        } else {
                          s0 = peg$FAILED;
                          if (peg$silentFails === 0) { peg$fail(peg$c35); }
                        }
                        if (s0 === peg$FAILED) {
                          if (input.substr(peg$currPos, 6) === peg$c7) {
                            s0 = peg$c7;
                            peg$currPos += 6;
                          } else {
                            s0 = peg$FAILED;
                            if (peg$silentFails === 0) { peg$fail(peg$c8); }
                          }
                          if (s0 === peg$FAILED) {
                            if (input.charCodeAt(peg$currPos) === 42) {
                              s0 = peg$c18;
                              peg$currPos++;
                            } else {
                              s0 = peg$FAILED;
                              if (peg$silentFails === 0) { peg$fail(peg$c19); }
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
        if (peg$c54.test(input.charAt(peg$currPos))) {
          s2 = input.charAt(peg$currPos);
          peg$currPos++;
        } else {
          s2 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c55); }
        }
        if (s2 !== peg$FAILED) {
          s3 = [];
          if (peg$c56.test(input.charAt(peg$currPos))) {
            s4 = input.charAt(peg$currPos);
            peg$currPos++;
          } else {
            s4 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c57); }
          }
          while (s4 !== peg$FAILED) {
            s3.push(s4);
            if (peg$c56.test(input.charAt(peg$currPos))) {
              s4 = input.charAt(peg$currPos);
              peg$currPos++;
            } else {
              s4 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c57); }
            }
          }
          if (s3 !== peg$FAILED) {
            peg$savedPos = s0;
            s1 = peg$c58(s2, s3);
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
      var s0, s1, s2;

      s0 = peg$currPos;
      s1 = [];
      if (peg$c59.test(input.charAt(peg$currPos))) {
        s2 = input.charAt(peg$currPos);
        peg$currPos++;
      } else {
        s2 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c60); }
      }
      if (s2 !== peg$FAILED) {
        while (s2 !== peg$FAILED) {
          s1.push(s2);
          if (peg$c59.test(input.charAt(peg$currPos))) {
            s2 = input.charAt(peg$currPos);
            peg$currPos++;
          } else {
            s2 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c60); }
          }
        }
      } else {
        s1 = peg$FAILED;
      }
      if (s1 !== peg$FAILED) {
        peg$savedPos = s0;
        s1 = peg$c61(s1);
      }
      s0 = s1;

      return s0;
    }

    function peg$parse_() {
      var s0, s1;

      s0 = [];
      if (peg$c62.test(input.charAt(peg$currPos))) {
        s1 = input.charAt(peg$currPos);
        peg$currPos++;
      } else {
        s1 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c63); }
      }
      while (s1 !== peg$FAILED) {
        s0.push(s1);
        if (peg$c62.test(input.charAt(peg$currPos))) {
          s1 = input.charAt(peg$currPos);
          peg$currPos++;
        } else {
          s1 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c63); }
        }
      }

      return s0;
    }

    function peg$parseStringLiteral() {
      var s0, s1, s2, s3;

      s0 = peg$currPos;
      if (peg$c64.test(input.charAt(peg$currPos))) {
        s1 = input.charAt(peg$currPos);
        peg$currPos++;
      } else {
        s1 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c65); }
      }
      if (s1 !== peg$FAILED) {
        s2 = [];
        if (peg$c66.test(input.charAt(peg$currPos))) {
          s3 = input.charAt(peg$currPos);
          peg$currPos++;
        } else {
          s3 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c67); }
        }
        if (s3 !== peg$FAILED) {
          while (s3 !== peg$FAILED) {
            s2.push(s3);
            if (peg$c66.test(input.charAt(peg$currPos))) {
              s3 = input.charAt(peg$currPos);
              peg$currPos++;
            } else {
              s3 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c67); }
            }
          }
        } else {
          s2 = peg$FAILED;
        }
        if (s2 !== peg$FAILED) {
          if (peg$c64.test(input.charAt(peg$currPos))) {
            s3 = input.charAt(peg$currPos);
            peg$currPos++;
          } else {
            s3 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c65); }
          }
          if (s3 !== peg$FAILED) {
            peg$savedPos = s0;
            s1 = peg$c68(s2);
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
