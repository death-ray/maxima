/* Parses a resolution proof */

crp(proof_list, assumptions) := block(
[ len: length(proof_list), from_lines:[], checked_clauses:[], numbers:[], last_clause:[], assumption_errors:[], deduction_errors:[] ],
for x in proof_list do (
  print("-------------------------------------------"),
  print("x = ",x, " last_clause = ",last_clause, " checked_clauses ",checked_clauses),
  if atom(x) then (
    /* The element was a number, we need to add it */
    numbers : endcons(x, numbers),
    print("  B1, numbers is ",numbers)),

  if is ((not (atom(x)) or is(x = proof_list[len])) and length(numbers) > 0 ) then (
    print("  B2, checking deduction"),
    /* The element was a clause and and we have elements in numbers OR the the element was a number and we are at the last line of the proof.
    Either way last_clause must be checked to see if it follows from the line numbers in numbers */
    deduced_clause : {},
    for num in numbers do (
      print("    adding in ",checked_clauses[num], " from ", checked_clauses),
      deduced_clause : union(deduced_clause, checked_clauses[num])),
    print("    deduced clause ", deduced_clause),
    /* Remove propositions and their negations */
    for y in deduced_clause do
      (if elementp(not y, deduced_clause) then
      deduced_clause : disjoin(not y, disjoin(y, deduced_clause))),
    print("    deduced_clause was cleaned up to be ", deduced_clause),
    /* TODO check if deduced clause is same as last clause */
    print("    last_clause is ",last_clause),
    lc : pop(last_clause),
    print("    lc is ",lc, "last_clause is ",last_clause),
    checked_clauses : endcons(lc, checked_clauses),
    print("    checked_clauses is now ", checked_clauses),
    numbers : []),
  if not atom(x) then ( /* The element is a clause */
    print("  B3, checking if assumption"),
    /* Check if the last_clause was an assumption */
    if (length(last_clause) > 0) then (
      lc : pop(last_clause),
      if not (member(lc, assumptions)) then (
        push(lc, assumption_errors))
      else
        print("    The clause, ",lc, " is assumed"),
        endcons(lc, checked_clauses)
      ),
      push(x, last_clause),
    print("    The last clause list is now ",last_clause)
    /*endcons(x, known_clauses)*/
  )
),
print("==========================================="),
print("checked clauses: ", checked_clauses, "-- assumption_errors: ", assumption_errors, "-- deduction_errors: ", deduction_errors)
)
