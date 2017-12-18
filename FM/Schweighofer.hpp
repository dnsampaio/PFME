#pragma once
#ifndef _SCHWEIGHOFER_HPP_
#define _SCHWEIGHOFER_HPP_

#include <glpk.h>
#include "Constraint.hpp"
#include <cassert>
#include <ginac/ginac.h>
#include <sstream>

#define MAX_ERROR 1.0e-7

using namespace std;
using namespace GiNaC;

template<typename T> using gexmap = map<ex, T, ex_is_less>;
typedef gexmap<unsigned> sysType;

/* The SchweighoferTester implements a positiveness test. For a given system of non-negative inequality constraints S = {E0 >= 0, E1 >= 0 ... En >= 0},
 * multiplying and adding their expressions always generate non-negative inequalities (E0^n*E^m >= 0). If an expression can be written by combining
 * any of these inequalities, multiplied by non-negative values, then the S implies E' is positive. The obvious inequality 1 >= 0 is also part of the
 * system of constraints. If, in the end, the system can generate that E' = ADD(MUL(E0...En)) + c*(1), where c >= 0, it means that E' is implied to be
 * positive by a distance of c. To determine each expression coefficient, constrainted to non-negative values, this problem is formulated as a linear
 * problem. Each row of the problem represent an monomial and each column an expression E(0..n). Each cell of the table tells the index of that monomial
 * in the given expression. The rhs column holds the coefficients of each monomial for the evaluated expression E' (or -E'), as a fixed value (LHS*x = RHS).
 * Each variable (column) must be non-negative. And our objective function is to maximaze x0, the coefficient that multiplies "1".
 *
 * Our tester evaluates both E' and -E' to determinate if either positive or negative sign is implied by the system. */

enum SIGN : unsigned char
{ //Possible signs our system S implies for a tested expression E'
  UNKNOWN = 0,   //Nor E or E' detected to be implied
  ZERO = 1,      //E' and -E' are both implied by the system by zero distance
  GTZ = 2,       //E' is implied by S by a distance > 0
  GEZ = 3,       //E' is implied by S by a distance = 0
  LTZ = 4,       //-E' is implied by S by a distance > 0
  LEZ = 5,       //-E' is implied by S by a distance = 0
  ABSURD = 7    //E' -c0 and -E' -c1 are both implied by the system, where at least one of c0 or c1 is greater than zero.
};

typedef struct
{
    SIGN sign;       //Return if the system implies an expressions holds this sign
    double distance; //Tells by how much the expression holds the given sign
} testResult;

struct SchweighoferTester
{
    typedef gexmap<int> exPos;

    SchweighoferTester(exset ineqs, unsigned d = 2);
    SchweighoferTester(const sysType &ineqs, unsigned d = 2);
    virtual ~SchweighoferTester();

    testResult test(ex ineq, bool testPosAndNeg = true);

    bool hasChanges() const;
    ostream &printResult(ostream &o, const bool printSteps = false) const;

    const exPos &getIneqs() const {
      return ineqPos;
    }

    const exPos &getMonomials() const {
      return monomPos;
    }
  private:
    testResult test_factorized(ex ineq);
    bool goodNumbers(const ex &compareTo) const;//Hack: The simplex algorithm might be interrupted due iteration/time limits, but it might already have good values (all columns >= 0). Use this to test such cases.
    bool isProved(int o, bool isExact = false, const ex &compareTo = 0 ) const;
    typedef map<int, map<int, double> > idx_map; //Maps monomials coefficients per expression. In Column x Row format, that is: map[Inequality|Column][Monomial|Row] = coefficient

    void gatherMonomials(const ex &ineq, gexmap<double> &coeffs);
    void expandSrcs(const exset &root, idx_map &indexes);
    void buildProblem(const idx_map &indexes);
    void clear();
    size_t numSrcs;
    glp_prob *problem;
    exPos monomPos; //Holds monomial positions on the glpk problem (row number)
    exPos ineqPos;  //Holds expressions position on the glpk problem (column number) !!!!!PS!!!! We do not hold numeric values. For example: 4N-3x+2 will turn into 4N-3x.
    unsigned order;
    unsigned MAX_ORDER;
    unsigned shrinkIterations;
};

namespace std
{
ostream &operator<<(ostream &out, const SIGN &s);
ostream &operator<<(ostream &out, const testResult &r);
}

#endif //_SCHWEIGHOFER_HPP_
