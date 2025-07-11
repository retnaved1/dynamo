/**
 * @name Regular expression matching on sensitive data with potential for ReDoS
 * @description Finds calls to 're' functions (match, search, findall, fullmatch, sub, subn, split)
 *              where the input string is derived from sensitive data.
 *              If the regex pattern is susceptible to catastrophic backtracking (ReDoS),
 *              its evaluation time can be exploited. This query flags the use of 're'
 *              on sensitive data; a separate ReDoS regex analyzer would be needed for the pattern itself.
 * @kind path-problem
 * @problem.severity warning
 * @id py/redos-on-sensitive-data
 * @tags security
 *       external/cwe/cwe-1333 // ReDoS
 *       external/cwe/cwe-208  // Timing Attack (indirectly)
 */

import python
import semmle.python.dataflow.new.DataFlow
import semmle.python.dataflow.new.TaintTracking
import semmle.python.Concepts

// Heuristic to identify sensitive data sources
class SensitiveTextSource extends DataFlow::Node {
  SensitiveTextSource() {
    exists(NameNode name | name = this.asName() |
      name.getId().regexpMatch("(?i).*(password|secret|token|key|apikey|auth|user_input|query|payload).*")
    )
    or
    // Parameters of functions that might handle sensitive text
    exists(Function f, Parameter param | this.asParameter() = param and f = param.getFunction() |
      f.getName().regexpMatch("(?i).*(authenticate|login|verify|authorize|decrypt|parse|process_request|handle_input).*") and
      param.getName().regexpMatch("(?i).*(password|secret|token|key|data|input|text|string|query).*")
    )
  }
}

// Configuration for taint tracking
class ReDoSConfig extends TaintTracking::Configuration {
  ReDoSConfig() { this = "ReDoSConfig" }

  override predicate isSource(DataFlow::Node source) {
    source instanceof SensitiveTextSource
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(CallNode callToRe |
      // re.match(pattern, string), re.search(pattern, string), re.fullmatch(pattern, string), re.split(pattern, string), re.findall(pattern, string)
      // re.sub(pattern, repl, string), re.subn(pattern, repl, string)
      // re.compile(pattern).match(string), etc.
      exists(AstNode func | func = callToRe.getFunction() |
        (
          // Direct calls like re.match()
          exists(AttributeNode attr | attr = func and attr.getObject().(NameNode).getId() = "re" |
            attr.getName().regexpMatch("match|search|fullmatch|split|findall|sub|subn")
          )
          or
          // Calls on compiled regex objects: regex_obj.match()
          exists(AttributeNode attr | attr = func |
            attr.getName().regexpMatch("match|search|fullmatch|split|findall|sub|subn") and
            exists(CallNode compileCall | compileCall.getFunction().(AttributeNode).getObject().(NameNode).getId() = "re" and
                                        compileCall.getFunction().(AttributeNode).getName() = "compile" and
                                        attr.getObject().pointsTo(compileCall)
            )
          )
        )
      )
    |
      // The 'string' argument is usually the second for re.func(pat, str) or first for compiled.func(str)
      (sink.asCfgNode() = callToRe.getArg(1) and callToRe.getFunction().(AttributeNode).getObject().(NameNode).getId() = "re") // re.func(pattern, SINK)
      or
      (sink.asCfgNode() = callToRe.getArg(2) and callToRe.getFunction().(AttributeNode).getObject().(NameNode).getId() = "re" and
        callToRe.getFunction().(AttributeNode).getName().regexpMatch("sub|subn")
      ) // re.sub/subn(pattern, repl, SINK)
      or
      (sink.asCfgNode() = callToRe.getArg(0) and // compiled_re.func(SINK)
       exists(AttributeNode attr | attr = callToRe.getFunction() |
            exists(CallNode compileCall | compileCall.getFunction().(AttributeNode).getObject().(NameNode).getId() = "re" and
                                        compileCall.getFunction().(AttributeNode).getName() = "compile" and
                                        attr.getObject().pointsTo(compileCall)
            )
        )
      )
    )
  }
}

from ReDoSConfig config, DataFlow::PathNode source, DataFlow::PathNode sink, CallNode callToRe
where
  config.hasFlowPath(source, sink) and
  exists(AstNode func | func = callToRe.getFunction() |
    (
      exists(AttributeNode attr | attr = func and attr.getObject().(NameNode).getId() = "re") or // direct re.func
      exists(AttributeNode attr | attr = func | // compiled_re.func
        exists(CallNode compileCall | compileCall.getFunction().(AttributeNode).getObject().(NameNode).getId() = "re" and
                                    compileCall.getFunction().(AttributeNode).getName() = "compile" and
                                    attr.getObject().pointsTo(compileCall)
        )
      )
    )
  ) and
  (
    (sink.asCfgNode() = callToRe.getArg(1) and callToRe.getFunction().(AttributeNode).getObject().(NameNode).getId() = "re") or
    (sink.asCfgNode() = callToRe.getArg(2) and callToRe.getFunction().(AttributeNode).getObject().(NameNode).getId() = "re" and
      callToRe.getFunction().(AttributeNode).getName().regexpMatch("sub|subn")) or
    (sink.asCfgNode() = callToRe.getArg(0) and
     exists(AttributeNode attr | attr = callToRe.getFunction() |
        exists(CallNode compileCall | compileCall.getFunction().(AttributeNode).getObject().(NameNode).getId() = "re" and
                                    compileCall.getFunction().(AttributeNode).getName() = "compile" and
                                    attr.getObject().pointsTo(compileCall)
            )
        )
    )
  )
select callToRe, source, sink,
  "Call to regex function at $@ uses sensitive data ($@) as input. "+
  "If the regex pattern is vulnerable to ReDoS, this could lead to excessive execution time.",
  callToRe, callToRe.getLocation().toString(),
  source.getNode(), source.getNode().toString()
