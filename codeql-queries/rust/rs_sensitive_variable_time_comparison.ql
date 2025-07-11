/**
 * @name Potentially non-constant time slice/string comparison for sensitive data
 * @description Finds direct slice or string comparisons (e.g., `==`, `!=`)
 *              involving potentially sensitive data, which might be vulnerable to timing attacks.
 *              Standard library functions like `eq` for slices are typically not constant time.
 * @kind path-problem
 * @problem.severity warning
 * @id rs/sensitive-variable-time-comparison
 * @tags security
 *       external/cwe/cwe-208
 */

import rust
import semmle.rust.dataflow.NewDataFlow
import semmle.rust.dataflow.NewTaintTracking
import semmle.rust.Values

// Heuristic to identify sensitive data sources
class SensitiveDataConfig extends NewTaintTracking::Configuration {
  SensitiveDataConfig() { this = "SensitiveDataConfig" }

  override predicate isSource(DataFlow::Node source) {
    exists(Parameter p | source.asParameter() = p |
      p.getName().regexpMatch("(?i).*(password|secret|token|key|apikey|auth).*")
      or
      exists(Function f | f = p.getFunction() |
        f.getName().regexpMatch("(?i).*(authenticate|login|verify|authorize|decrypt|check_password).*") and
        p.getName().regexpMatch("(?i).*(password|secret|token|key|data).*")
      )
    )
    or
    // Variables initialized with sensitive-looking names
    exists(LocalVariableDeclExpr lvd | source.asDefiningValue(lvd.getVariable()) = lvd.getVariable().getADefiningValue() |
        lvd.getVariable().getName().regexpMatch("(?i).*(password|secret|token|key|apikey|auth).*")
    )
  }

  override predicate isSink(DataFlow::Node sink) {
    // Sink is an operand of a comparison operation
    exists(EqualityOperation eqOp | sink.asExpr() = eqOp.getAnOperand() |
        not eqOp.getAnOperand().(Value).isCompileTimeConstant() // Exclude comparisons with constants if desired, though one side being constant doesn't make it safe
    )
  }

  override predicate isSanitizer(DataFlow::Node node) {
    // Example: explicit constant-time comparison function calls
    exists(CallExpr call |
        call.getFullyQualifiedName() = "constant_time_compare" and // Replace with actual constant-time functions
        node.asExpr() = call.getAnArgument()
    )
    or
    // Calls to known constant-time crypto libraries (e.g. `subtle::ConstantTimeEq`)
    exists(CallExpr call |
        call.getFullyQualifiedName().regexpMatch("(?i).*subtle.*ConstantTimeEq.*") and
        node.asExpr() = call.getAnArgument()
    )
  }
}

from SensitiveDataConfig config, DataFlow::PathNode source, DataFlow::PathNode sink
where config.hasFlowPath(source, sink)
select sink.getNode().asExpr(), source, sink,
  "Comparison involving sensitive data ($@) might not be constant time.",
  source.getNode().asExpr(), source.getNode().asExpr().toString()
