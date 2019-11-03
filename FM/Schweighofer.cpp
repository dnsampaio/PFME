#include "Schweighofer.hpp"
#include "debug.hpp"
#include <cmath>
#include <iostream>
using namespace std;
using namespace GiNaC;

template <typename T> using gexmap = map<ex, T, ex_is_less>;

SchweighoferTester::SchweighoferTester(exset ineqs, unsigned d)
    : numSrcs(ineqs.size()), problem(nullptr), monomPos({}), ineqPos({}),
      order(0), MAX_ORDER(std::max(1u, d)) {
  // We do a very basic test to avoid doing work for the obvious systems
  if (numSrcs == 0) {
    DEBUG(5, "Empty system == true\n");
    return;
  }
  for (exset::iterator i = ineqs.begin(), iEnd = ineqs.end(); i != iEnd;) {
    const ex &e = *i;
    if (is_a<numeric>(e)) {
      if (e < 0) {
        DEBUG(5, e << u8" ≥ 0 ⇒ false\n");

        clear();
        return;
      }
      DEBUG(5, e << u8" ≥ 0 ⇒ true; ignoring\n");
      auto ni = std::next(i);
      ineqs.erase(i);
      iEnd = ineqs.end();
      i = ni;
      numSrcs--;
    }
    i++;
    DEBUG(5, e << " == added new constraint\n");
  }
  idx_map indexes;
  expandSrcs(ineqs, indexes);
  DEBUG(4, indexes.size() << " number of distinct inequalities\n");
  ineqs.clear();
  buildProblem(indexes);
  indexes.clear();
  glp_term_out(GLP_OFF);
  DEBUGIF(8, "Enabling glpk output\n") { glp_term_out(GLP_ON); }
}

SchweighoferTester::SchweighoferTester(const sysType &ineqs, unsigned d)
    : numSrcs(ineqs.size()), problem(nullptr), monomPos({}), ineqPos({}),
      order(0), MAX_ORDER(std::max(1u, d)) {
  exset ns;
  for (const auto i : ineqs)
    ns.insert(i.first);

  for (exset::iterator i = ns.begin(), iEnd = ns.end(); i != iEnd;) {
    const ex &e = *i;
    if (is_a<numeric>(e)) {
      if (e < 0) {
        DEBUG(5, e << u8" ≥ 0 ⇒ false\n");

        clear();
        return;
      }
      DEBUG(5, e << u8" ≥ 0 ⇒ true; ignoring\n");
      auto ni = std::next(i);
      ns.erase(i);
      iEnd = ns.end();
      i = ni;
      numSrcs--;
    }
    i++;
    DEBUG(5, e << " == added new constraint\n");
  }
  idx_map indexes;
  expandSrcs(ns, indexes);
  DEBUG(4, indexes.size() << " number of distinct inequalities\n");
  ns.clear();
  buildProblem(indexes);
  indexes.clear();
  glp_term_out(GLP_OFF);
  DEBUGIF(7, "Enabling glpk output\n") { glp_term_out(GLP_ON); }
}

SchweighoferTester::~SchweighoferTester() { clear(); }

bool SchweighoferTester::goodNumbers(const ex &compareTo) const {
  if (glp_get_col_prim(problem, 1) < -0.990 - MAX_ERROR) {
    DEBUG(4, "FIXME!!! GLP getting col_prim[1] < -0.990");
    return false;
  }
  for (int s = 2, e = glp_get_num_cols(problem); s <= e; s++) {
    if (glp_get_col_prim(problem, s) < -MAX_ERROR) {
      DEBUG(4, "FIXME!!! GLP getting col_prim["
                   << s << "] == " << glp_get_col_prim(problem, s) << NL);
      return false;
    }
  }

  ex res = 0;
  for (const auto &col : ineqPos) {
    double c = glp_get_col_prim(problem, col.second);
    if ((c < -MAX_ERROR) or (c > MAX_ERROR)) {
      DEBUG(6, res << " += " << col.first << "* (" << c << ")\n");
    }
    res += col.first * c;
  }
  res = expand(res);
  DEBUG(5, res << NL);
  ex final = expand(compareTo - res);
  if (is_a<numeric>(final)) {
    if ((final < MAX_ERROR) && (final > -MAX_ERROR))
      return true;
  } else if (is_a<add>(final)) {
    bool ok = true;
    for (const ex &op : final) {
      numeric coeff = op.integer_content();
      if (!((coeff < MAX_ERROR) && (coeff > -MAX_ERROR))) {
        ok = false;
        break;
      }
    }
    if (ok)
      return true;
  } else {
    numeric c = final.integer_content();
    if ((c < MAX_ERROR) && (c > -MAX_ERROR))
      return true;
  }
  //  cerr << __FILENAME__ << "::" << __func__ << "::" << __LINE__ << "::FIX
  //  ME!!!\n\tTesting if " << compareTo << GE << "0, we got that " << res << GE
  //  << "0; difference is: " << final
  //      << " that has error bigger than " << MAX_ERROR << NL;
  /* TODO: If here, it means glpk did solve the problem but there is possibly:
   * 1) Error in formulation of the problem or
   * 2) glpk is in a error state
   * 3) Did call this function with bad arguments
   */
  return false;
}

bool SchweighoferTester::isProved(int o, bool isExact,
                                  const ex &compareTo) const {
  if (o != 0) {
    switch (o) {
    case GLP_EBADB:
      DEBUG(8, "GLP_EBADB: Unable to start the search, because the "
               "initial\nbasis specified in the problem object is invalid—the "
               "number of\nbasic (auxiliary and structural) variables is not "
               "the same as\nthe number of rows in the problem object.\n");
      break;
    case GLP_ESING:
      DEBUG(8,
            "GLP_ESING: Unable to start the search, because the basis\nmatrix "
            "corresponding to the initial basis is exactly singular.\n");
      break;
    case GLP_EBOUND:
      DEBUG(8, "GLP_EBOUND: Unable to start the search, because some "
               "double-bounded\n(auxiliary or structural) variables have "
               "incorrect bounds.\n");
      break;
    case GLP_EFAIL: {
      DEBUG(8, "GLP_EFAIL The problem instance has no rows/columns.\n");
      if (!isExact)
        return true; // Hack to handle GLPK bug:
                     // https://lists.gnu.org/archive/html/bug-glpk/2016-02/msg00002.html
      assertM(false, "Why???\n");
      break;
    }
    case GLP_EITLIM:
      DEBUG(8, "GLP_EITLIM: The search was prematurely terminated, "
               "because\nthe simplex iteration limit has been exceeded.\n");
      return goodNumbers(compareTo);
      break;
    case GLP_ETMLIM:
      DEBUG(8, "The search was prematurely terminated, because the time "
               "limit\nhas been exceeded.\n");
      return goodNumbers(compareTo);
      break;
    default:
      break;
    }
    return false;
  }

  o = glp_get_status(problem);
  if (not((o == GLP_FEAS) or (o == GLP_OPT))) {
    switch (o) {
    case GLP_INFEAS: {
      DEBUG(8, "GLP_INFEAS — solution is infeasible\n");
      break;
    }
    case GLP_NOFEAS: {
      DEBUG(8, "GLP_NOFEAS — problem has no feasible solution\n");
      break;
    }
    case GLP_UNBND: {
      DEBUG(8, "GLP_UNBND — problem has unbounded solution\n");
      break;
    }
    case GLP_UNDEF: {
      DEBUG(8, "GLP_UNDEF\n");
      break;
    }
    default:
      break;
    }
    return false;
  }

  o = glp_get_prim_stat(problem);
  if (o != GLP_FEAS) {
    switch (o) {
    case GLP_UNDEF: {
      DEBUG(8, "GLP_UNDEF  — primal solution is undefined      \n");
      break;
    }
    case GLP_FEAS: {
      DEBUG(8, "GLP_FEAS   — primal solution is feasible       \n");
      break;
    }
    case GLP_INFEAS: {
      DEBUG(8, "GLP_INFEAS — primal solution is infeasible     \n");
      break;
    }
    case GLP_NOFEAS: {
      DEBUG(8, "GLP_NOFEAS — no primal feasible solution exists\n");
      break;
    }
    default:
      break;
    }
    return false;
  }

  if (!isExact)
    return true;

  return goodNumbers(compareTo);
}
testResult SchweighoferTester::test_factorized(ex ineq) {
  DEBUG(6, "Factorizing " << ineq << " for obtaining sign\n");
  assertM(not is_a<numeric>(ineq), "Can't factorize a number");
  if (is_a<power>(ineq)) {
    power p = ex_to<power>(ineq);
    assertM(is_a<numeric>(p.op(1)),
            "Power " << p << " has non numeric exponent!!\n");
    numeric exp = ex_to<numeric>(p.op(1));
    assertM(exp.is_integer(),
            "Power " << p << " has non integer exponent " << exp << "!!\n");
    assertM(exp.is_nonneg_integer(),
            "Power " << p << " has negative integer exponent " << exp
                     << "!!\n");
    testResult sub = test(p.op(0));
    switch (sub.sign) {
    case SIGN::ZERO:
    case SIGN::ABSURD:
    case SIGN::GEZ:
      return sub;
    case SIGN::UNKNOWN:
    case SIGN::LEZ: {
      if (exp.is_even())
        return {SIGN::GEZ, 0.0};
      return sub;
    }
    case SIGN::LTZ: {
      if (exp.is_even())
        return {SIGN::GTZ, pow(sub.distance, exp.to_double())};
      return {SIGN::LTZ, pow(sub.distance, exp.to_double())};
    }
    case SIGN::GTZ: {
      return {SIGN::GTZ, pow(sub.distance, exp.to_double())};
    }
    }
  }
  if (is_a<power>(expand(-ineq))) {
    ineq = expand(-ineq);
    power p = ex_to<power>(ineq);
    assertM(is_a<numeric>(p.op(1)),
            "Power " << p << " has non numeric exponent!!\n");
    numeric exp = ex_to<numeric>(p.op(1));
    assertM(exp.is_integer(),
            "Power " << p << " has non integer exponent " << exp << "!!\n");
    assertM(exp.is_nonneg_integer(),
            "Power " << p << " has negative integer exponent " << exp
                     << "!!\n");
    testResult sub = test(p.op(0));
    switch (sub.sign) {
    case SIGN::ZERO:
    case SIGN::ABSURD:
      return sub;
    case SIGN::UNKNOWN:
      if (exp.is_even())
        return {SIGN::LEZ, 0.0};
      return sub;
    case SIGN::GEZ:
      return {SIGN::LEZ, 0.0};
    case SIGN::LEZ: {
      if (exp.is_even())
        return {SIGN::LEZ, 0.0};
      return {SIGN::GEZ, 0.0};
    }
    case SIGN::LTZ: {
      if (exp.is_even())
        return {SIGN::LTZ, pow(sub.distance, exp.to_double())};
      return {SIGN::GTZ, pow(sub.distance, exp.to_double())};
    }
    case SIGN::GTZ: {
      return {SIGN::LTZ, pow(sub.distance, exp.to_double())};
    }
    }
  }
  ineq = factor(ineq);
  if (is_a<mul>(ineq)) {
    bool positive = true;
    double distance = 1.0;
    for (const ex &op : ineq) {
      testResult t = test(op);
      switch (t.sign) {
      case SIGN::ABSURD:
      case SIGN::UNKNOWN:
      case SIGN::ZERO:
        return t;
      case SIGN::LTZ: {
        positive = not positive;
        distance *= t.distance;
        break;
      }
      case SIGN::LEZ: {
        positive = not positive;
        distance = 0.0;
        break;
      }
      case SIGN::GTZ: {
        distance *= t.distance;
        break;
      }
      case SIGN::GEZ:
        distance = 0.0;
      }
    }
    if (positive) {
      if (distance > 0.0)
        return {SIGN::GTZ, distance};
      return {SIGN::GEZ, 0.0};
    }
    if (distance > 0.0)
      return {SIGN::LTZ, distance};
    return {SIGN::LEZ, 0.0};
  }
  return {SIGN::UNKNOWN, 0.0};
}

testResult SchweighoferTester::test(ex ineq, bool testPosAndNeg) {
  DEBUG(6, "Testing " << ineq << NL);
  testResult result = {SIGN::UNKNOWN, 0.0};
  ineq = expand(ineq);

  glp_set_col_bnds(problem, 1, GLP_DB, -0.9990, 1.0e6);
  glp_set_obj_coef(problem, 1, 1);
  for (int i = 2; i <= glp_get_num_cols(problem); i++)
    glp_set_col_bnds(problem, i, GLP_LO, 0.0, 0.0);

  for (int i = 1, iEnd = monomPos.size(); i <= iEnd; i++)
    glp_set_row_bnds(problem, i, GLP_FX, 0.0, 0.0);

  bool isNumeric = false;

  if (is_a<numeric>(ineq)) {
    DEBUG(6, "It is a numeric constant\n");
    double max = ex_to<numeric>(ineq).to_double();
    max = std::abs(max);
    max += 5.0;
    glp_set_col_bnds(problem, 1, GLP_DB, 0.0, max);
    DEBUG(7, ineq << " is a numeric value\n");
    isNumeric = true;
    if (ineq < 0.0000000001 && ineq > -0.0000000001) {
      DEBUG(6, "It is zero");
      DEBUG(7, ineq << " is 0\n");
      return {SIGN::ZERO, 0.0};
    } else if (ineq < 0) {
      glp_set_col_bnds(problem, 1, GLP_FX, 0.0, 0.0);

      result = {SIGN::LTZ, -(ex_to<numeric>(ineq).to_double())};
      DEBUG(7, ineq << " is negative number\n");
    } else {
      DEBUG(7, ineq << " is positive number\n");
      return {SIGN::GTZ, (ex_to<numeric>(ineq).to_double())};
    }
  } else {
    DEBUG(6, "Testing if we have the expression being tested, by a different "
             "constant\n");
    bool gez = false, lez = false;
    double gtz = 0.0, ltz = 0.0;
    for (const auto &toTest : ineqPos) {
      DEBUG(9, "Testing if " << toTest.first << " implies " << ineq << NL);
      ex pos_test = expand(ineq - toTest.first);
      bool this_gez = is_a<numeric>(pos_test) and (pos_test >= 0.0);
      if (this_gez) {
        gez = true;
        gtz = max(gtz, (gez ? ex_to<numeric>(pos_test).to_double() : 0.0));
      }
      DEBUG(9, "gez? " << gez << "; gtz? " << gtz << NL);
      if (testPosAndNeg) {
        ex neg_test = expand(ineq + toTest.first);
        bool this_lez = is_a<numeric>(neg_test) and (neg_test <= 0.0);
        if (this_lez) {
          lez = true;
          ltz = max(ltz, (lez ? -ex_to<numeric>(neg_test).to_double() : 0.0));
        }
        DEBUG(9, "lez? " << lez << "; ltz? " << ltz << NL);
      }
    }
    if (gez or lez) {
      if (((ltz > 0.0) and gez) or ((gtz > 0.0) and lez)) {
        DEBUG(6, "Linear test returning absurd for ineq " << ineq << NL)
        return {SIGN::ABSURD, 0.0};
      }

      if (lez and gez) {
        result = {SIGN::ZERO, 0.0};
        DEBUG(6, "Linear test making sign of " << ineq << result << NL)
      }

      if (gez) {
        if (gtz > 0.0) {
          result = {SIGN::GTZ, gtz};
          DEBUG(6, "Linear test making sign of " << ineq << result << NL)
        } else {
          result = {SIGN::GEZ, 0.0};
          DEBUG(6, "Linear test making sign of " << ineq << result << NL)
        }
      } else {
        if (ltz > 0.0) {
          result = {SIGN::LTZ, ltz};
          DEBUG(6, "Linear test making sign of " << ineq << result << NL)

        } else {
          result = {SIGN::LEZ, 0.0};
          DEBUG(6, "Linear test making sign of " << ineq << result << NL)
        }
      }
    }
  }
  gexmap<double> monomialsCoeffs;
  gatherMonomials(ineq, monomialsCoeffs);

  for (const auto &mon : monomialsCoeffs) {
    auto it = monomPos.find(mon.first);
    if (it == monomPos.end()) {
      DEBUG(3, "Monomial: " << mon.first << " is not in the st system.\n");
      monomialsCoeffs.clear();
      return {SIGN::UNKNOWN, 0};
    }
    glp_set_row_bnds(problem, it->second, GLP_FX, mon.second, mon.second);
    DEBUG(7, "glp_set_row_bnds: " << it->second << '(' << it->first
                                  << ") == " << mon.second << "\n");
  }
  if (!testPosAndNeg)
    monomialsCoeffs.clear();

  glp_smcp config;
  glp_init_smcp(&config);

  //  config.tol_bnd = 1.0e-9; //Tolerance used to check if the basic solution
  //  is primal feasible. config.tol_piv = 1.0e-11; //Tolerance used to choose
  //  eligble pivotal elements of the simplex table.
  config.it_lim = 10000;
  config.tm_lim = 600;
  //  glp_write_prob(problem, 0, "problem.txt");
  int o = glp_simplex(problem, &config);
  if (!isProved(o)) {
    if (!testPosAndNeg) {
      if (result.sign == SIGN::UNKNOWN)
        return test_factorized(ineq);
      return result;
    }
  } else {
    //    glp_write_prob(problem, 0, "problem.txt");
    o = glp_exact(problem, &config);
    if (!isProved(o, true, ineq)) {
      if (!testPosAndNeg) {
        if (result.sign == SIGN::UNKNOWN)
          return test_factorized(ineq);
        return result;
      }
    } else {
      double colPrim = glp_get_col_prim(problem, 1);
      if (0.0000001 < colPrim) {
        result.sign = SIGN::GTZ;
        result.distance = colPrim;
      } else if (-0.99999999 < colPrim) {
        if (result.sign != SIGN::ZERO) {
          result.sign = SIGN::GEZ;
          result.distance = colPrim;
        }
      } else
        assert(false); //??? Forced it to be >= -0.9999999
      if (isNumeric) { // If it was proved E >= 0, and E is a numeric, then
                       // distance == E, else it is an absurd! (or bug???)
        if (colPrim != result.distance) {
          cerr << __FILENAME__ << "::" << __func__ << "::" << __LINE__
               << ":: Proved that" << ineq << " is " << result << NL;
          printResult(cerr, true);
          return {SIGN::ABSURD, 0.0};
        }
      }
    }
  }
  // Test -E >= 0? Must not test a -E >= 0, obvious response no?
  if ((!testPosAndNeg) or
      isNumeric) { // It was requested to verify E >= 0 and -E >= 0?
    if (result.sign == SIGN::UNKNOWN)
      return test_factorized(ineq);

    return result;
  }

  for (int i = 1, iEnd = monomPos.size(); i <= iEnd; i++)
    glp_set_row_bnds(problem, i, GLP_FX, 0.0, 0.0);

  for (const auto &mon : monomialsCoeffs) {
    auto it = monomPos.find(mon.first);
    glp_set_row_bnds(problem, it->second, GLP_FX, -mon.second, -mon.second);
    DEBUG(7, "glp_set_row_bnds: " << it->second << '(' << it->first
                                  << ") == " << -mon.second << "\n");
  }
  monomialsCoeffs.clear();
  //  glp_write_prob(problem, 0, "problem.txt");
  o = glp_simplex(problem, &config);
  if (!isProved(o)) {
    if (result.sign == SIGN::UNKNOWN)
      return test_factorized(ineq);
    return result;
  }
  //  glp_write_prob(problem, 0, "problem.txt");
  o = glp_exact(problem, &config);
  if (!isProved(o, true, expand(-ineq))) {
    if (result.sign == SIGN::UNKNOWN)
      return test_factorized(ineq);

    return result;
  }

  double colPrim = glp_get_col_prim(problem, 1);
  switch (result.sign) {
  case SIGN::ZERO:
  case SIGN::GEZ:
    if (colPrim < 1.0)
      return result;
    break;
  case SIGN::GTZ:
    return {SIGN::ABSURD, 0.0};
    break;
  case SIGN::LTZ:
    if (result.distance != colPrim)
      return {SIGN::ABSURD, 0.0};
    break;
  default:
    break;
  }

  if (colPrim >= 1.0)
    return {SIGN::LTZ, colPrim};
  else if (-0.99999999 < colPrim)
    return {SIGN::LEZ, colPrim};
  else
    assert(false); //??? Forced it to be >= -0.9999999

  if (result.sign == SIGN::UNKNOWN)
    return test_factorized(ineq);

  return result;
}

void SchweighoferTester::gatherMonomials(const ex &ineq,
                                         gexmap<double> &coeffs) {
  if (is_a<numeric>(ineq)) {
    DEBUG(9, ineq << " is integer number " << ex_to<numeric>(ineq).to_double()
                  << "\n");
    coeffs[1] = ex_to<numeric>(ineq).to_double();
    return;
  }
  if (is_a<symbol>(ineq) or is_a<power>(ineq)) {
    DEBUG(9, ineq << " is a symbol/power, thus 1 * " << ineq << "\n");
    coeffs[ineq] = 1;
    return;
  }
  if (is_a<mul>(ineq)) {
    numeric c = 1;
    for (const ex &op : ineq) {
      if (is_a<numeric>(op)) {
        assert(c == 1);
        c = ex_to<numeric>(op);
      }
    }
    ex monomial;
    if (!divide(ineq, c, monomial))
      assert(false);

    coeffs[monomial] = c.to_double();
    DEBUG(9, ineq << " is a monomial " << c.to_double() << " * " << monomial
                  << "\n");
    return;
  }
  assert(is_a<add>(ineq));
  DEBUG(9, ineq << " is a add expression\n");
  for (const ex &op : ineq)
    gatherMonomials(op, coeffs);
  DEBUGFOR(9, const auto &sub
           : coeffs, ineq << " is a add monomial " << sub.second << " * "
                          << sub.first << "\n");
}

// TODO: 1: Remove constant from ineq map, ex: 4x + 3yz -2 >= 0; remove the
// numerical [ -2 ] value. 2: Keep map of these new expressions to their relative
// numeric value: map[4x + 3yz] = -2 3: When testing 4x + 3yz -1, we also
// decompose as [4x + 3yz][-1]. As the tester has that map[[4x + 3yz] = -2 < -1,
// our starting test value is already {GTZ, 1}.

void SchweighoferTester::expandSrcs(const exset &root, idx_map &indexes) {
  map<int, exset> expanded;
  // Order 0: S^0 = { 1 }        ; Is fixed and constant
  // Order 1: S^1 = S            ; Is just the input system
  // Order 2: S^2 = S * S;       ; Multiply the system by it self
  // Order N: S^N = S * S ^ (N-1); Multiply the system by the last generated
  // degree to obtain the next one

  expanded[0] = {ex(1)};
  monomPos[1] = 1;
  ineqPos[1] = 1;
  indexes[1][1] = 1;
  for (unsigned order = 1; order <= MAX_ORDER; order++) {
    DEBUG(8, "Inserting constraints at order " << order << NL);
    for (const ex &rootExp : root) {
      DEBUG(8, "rootExp: " << rootExp << NL);
      for (const ex &prevOrd : expanded[order - 1]) {
        DEBUG(8, "prevOrd = " << prevOrd << NL);
        ex expanExp = expand(rootExp * prevOrd, 15);
        bool skip = false;
        for (const auto atOrder : expanded) {
          if (atOrder.second.find(expanExp) != atOrder.second.end()) {
            DEBUG(8, expanExp << " is already existent at degree "
                              << atOrder.first)
            skip = true;
            break;
          }
        }
        if (skip)
          continue;
        DEBUG(7, "Adding constraint " << expanExp << NL);
        expanded[order].insert(expanExp);
        unsigned column = indexes.size() + 1;
        DEBUG(7, "\t" << expanExp << " is at column " << column << NL);
        ineqPos[expanExp] = column;
        gexmap<double> monomialsCoeffs;
        gatherMonomials(expanExp, monomialsCoeffs);
        assert(monomialsCoeffs.size());
        for (const auto &coefficient : monomialsCoeffs) {
          size_t row = monomPos[coefficient.first];
          if (row == 0) {
            row = monomPos.size();
            monomPos[coefficient.first] = row;
          }
          indexes[column][row] = coefficient.second;
        }
        monomialsCoeffs.clear();
        if (column >= 2500)
          return;
      }
    }
  }
}

void SchweighoferTester::buildProblem(const idx_map &indexes) {
  if (problem != nullptr) {
    clear();
    problem = nullptr;
  }
  problem = glp_create_prob();
  assert(nullptr != problem);
  assert((indexes.size()) == ineqPos.size()); // glpk starts vectors from 1
  assert(indexes.size());
  const size_t nCols = ineqPos.size(), nRows = monomPos.size();
  glp_add_cols(problem, nCols);
  glp_add_rows(problem, nRows);
  for (const auto &mono : monomPos) {
    stringstream ss;
    ss << mono.first;
    glp_set_row_name(problem, mono.second, ss.str().c_str());
  }
  for (const auto &ineq : ineqPos) {
    //    stringstream ss;
    //    ss << ineq.first;
    //    glp_set_col_name(problem, ineq.second, ss.str().c_str());

    size_t nCoeffs = indexes.find(ineq.second)->second.size();
    vector<int> is;
    vector<double> vs;
    is.push_back(0); // glpk ignores element [0]
    vs.push_back(0); // glpk ignores element [0]
    for (const auto &monomCoeff : indexes.find(ineq.second)->second) {
      is.push_back(monomCoeff.first);
      vs.push_back((double)monomCoeff.second);
    }
    glp_set_mat_col(problem, ineq.second, nCoeffs, is.data(), vs.data());
    glp_set_col_bnds(problem, ineq.second, GLP_LO, 0.0000, 0);
    glp_set_obj_coef(problem, ineq.second, 0);
    is.clear();
    vs.clear();
  }

  glp_set_obj_dir(problem, GLP_MAX);
  glp_set_obj_coef(problem, 1, 1);
  //  glp_set_col_bnds(problem, 1, GLP_DB, -0.99999990, 1.85e18);
}

void SchweighoferTester::clear() {
  numSrcs = 0;
  monomPos.clear();
  ineqPos.clear();
  if (problem) {
    glp_delete_prob(problem);
    problem = nullptr;
  }
}

ostream &SchweighoferTester::printResult(ostream &o,
                                         const bool printSteps) const {
  ex res = 0;
  string front = "   ";
  for (const auto &col : ineqPos) {
    double c = glp_get_col_prim(problem, col.second);
    if (c != 0.0) {
      res += col.first * c;
      if (printSteps) {
        o << front << '(' << std::setprecision(19) << c << ")*(" << col.first
          << ")\n";
        front = " + ";
      } else {
        DEBUG(4, res << " += " << col.first << "* (" << c << ")\n");
      }
    }
  }
  res = expand(res);
  DEBUG(5, res << NL);
  ex final = 0;
  if (is_a<symbol>(res)) {
    final = res;
  } else if (is_a<numeric>(res)) {
    if ((res > MAX_ERROR) or (res < -MAX_ERROR))
      final = res;
  } else if (is_a<add>(res)) {
    for (const ex &op : res) {
      numeric coeff = op.integer_content();
      if ((coeff > -MAX_ERROR) && (coeff < MAX_ERROR))
        continue;
      final += op;
    }
  } else {
    numeric coeff = res.integer_content();
    if (!(coeff > -MAX_ERROR) && (coeff < MAX_ERROR))
      final = res;
  }
  if (printSteps)
    return o << " = " << final << NL;

  return o << final << NL;
}

namespace std {

ostream &operator<<(ostream &out, const SIGN &s) {
  switch (s) {
  case SIGN::ABSURD:
    out << "ABSURD";
    break;
  case SIGN::GEZ:
    out << "GEZ";
    break;
  case SIGN::GTZ:
    out << "GTZ";
    break;
  case SIGN::LEZ:
    out << "LEZ";
    break;
  case SIGN::LTZ:
    out << "LTZ";
    break;
  case SIGN::UNKNOWN:
    out << "UNKNOWN";
    break;
  case SIGN::ZERO:
    out << "ZERO";
    break;
  }
  return out;
}

ostream &operator<<(ostream &out, const testResult &r) {
  return out << '{' << r.sign << ", " << r.distance << "}";
}
} // namespace std
