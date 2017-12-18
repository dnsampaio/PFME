#pragma once
#ifndef _CONJUNCTION_HPP_
#define _CONJUNCTION_HPP_

#include "Constraint.hpp"

#include <iostream>
#include <set>

using namespace std;
using namespace GiNaC;
class Conjunction
{
  public:
    static Conjunction obvious, absurd;

    Symbols vars, pars;
    Constraints eqs, ineqs;

    Conjunction();

    static Conjunction Make(bool val);
    Conjunction(const Symbols &v, const Symbols &p, const Constraints &e, const Constraints &i, const unsigned id);
    Conjunction(string &in);

    Conjunction &operator=(const Conjunction &o){
      *this = o;
      return *this;
    }
    bool hasInverseConstraints() const;
    ostream &print(ostream& out) const;
    ostream &c_print(ostream& out) const;
    void insert(const string &constraint);

    void removeUnused();
    void removeUnused(Symbols &toSimplify);
    bool operator==(const Conjunction &other) const;
    bool hasVariables() const;
    static int degree(const ex &e);
    static int degree(cc e);

    Constraints::const_iterator begin() const{
      return ineqs.begin();
    }

    Constraints::const_iterator end() const{
      return ineqs.end();
    }

    unsigned size() const{
      return 2 * eqs.size() + ineqs.size();
    }

    bool hasEqs() const;
    bool empty() const;

    unsigned id() const{
      return _id;
    }
    ;
  protected:
    void detectEqs(){
      for ( cc c : ineqs ){
        cc iC = Constraint::get(-c->exp, false);
        if ( ineqs.find(iC) == ineqs.end() )
          continue;
        eqs.insert(Constraint::get(c->exp, true));
        ineqs.erase(iC);
        ineqs.erase(c);
      }
    }
    void makeFalse();
    void variablesStr2set(string &str, Symbols &s);
    static unsigned counter;
    const unsigned _id;
    bool linear;
};

ostream &operator<<(ostream &out, const Conjunction &c);

#endif //_CONJUNCTION_HPP_
