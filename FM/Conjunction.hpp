#pragma once
#ifndef _CONJUNCTION_HPP_
#define _CONJUNCTION_HPP_

#include "Constraint.hpp"
#include "Schweighofer.hpp"

#include <iostream>
#include <set>

#ifndef NL
#define NL std::endl
#endif
class Conjunction
{
  public:
    static Conjunction obvious, absurd;

    Symbols vars, pars;
    Constraints eqs, ineqs;
    SchweighoferTester * tester = nullptr;

    Conjunction();
    void clearTester(){
      if ( tester != nullptr ){
        delete tester;
        tester = nullptr;
      }
    }

    ~Conjunction(){
      clearTester();
      vars.remove_all();
      pars.remove_all();
      eqs.clear();
      ineqs.clear();
    }

    SchweighoferTester* getTester(){
      if ( tester == nullptr ){
        exset sys;
        if ( Conjunction::absurd == *this )
          sys.insert(-1);
        else if ( !( Conjunction::obvious == *this ) ){
          for ( cc c : ineqs )
            sys.insert(c->exp);
          for ( cc c : eqs ){
            sys.insert(c->exp);
            sys.insert(-c->exp);
          }
        }
        tester = new SchweighoferTester(sys);
      }
      return tester;
    }
    static Conjunction Make(bool val);
    Conjunction(const Symbols &v, const Symbols &p, const Constraints &e, const Constraints &i, const unsigned id);
    Conjunction(const Symbols &v, const Symbols &p, const Constraints &c, const unsigned id);
    Conjunction(std::string &in);

    std::ostream &print(std::ostream& out) const;
    ostream &c_print(ostream& out) const;
    void insert(const std::string &constraint);
    void rebuild(const exset &s){//Assume no variables where eliminated!!!!!!
      eqs.clear();
      ineqs.clear();
      for ( const ex &e : s){
        if ( s.find(-e) != s.end() )
          eqs.insert(Constraint::get(e, true));
        else
          ineqs.insert(Constraint::get(e, false));
      }
    };
    bool implies(const Conjunction &other);


//    bool factorizeEqs();
//    bool removeEqs(bool userPars = false);
    void removeUnused();
    void removeUnused(Symbols &toSimplify);
//    void removeRedundancy(const unsigned maxOr = 0, const unsigned maxSrcs = 0);
//    Conjunction simplify(const unsigned maxOr = 0, const unsigned maxSrcs = 0) const;
    bool operator==(const Conjunction &other) const;
    bool hasVariables() const;

    unsigned size() const{
      return 2 * eqs.size() + ineqs.size();
    }

    Conjunction operator&(const Conjunction &other) const;
    Conjunction operator&(const cc c) const;
    Conjunction operator&(const Constraints &clauses) const;
    bool removeJoin(const Constraints &toRemove, const Constraints &toJoin);
    void operator=(const Conjunction &other){
      vars = other.vars;
      pars = other.pars;
      eqs = other.eqs;
      ineqs = other.ineqs;
//      buildTester();
    }

    Conjunction(const Conjunction & other) :
        _id(other._id){
      *this = other;
    }
    bool hasInverseConstraints() const;
    bool hasEqs() const;
    bool empty() const;
    unsigned id() const{
      return _id;
    }
    ;
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

    int polynomialDegree(const ex &e, bool considerPars = true ) const {
      if ( is_a<numeric>(e) )
        return 0;

      if ( is_a<symbol>(e)){
        if ( considerPars or vars.has(e))
          return 1;
        return 0;
      }
      if ( is_a<power>(e) ){
        const power &p = ex_to<power>(e);
        assertM(is_a<numeric>(p.op(1)), e << " is a power with non-numeric exponent, don't know how to retrieve the degree!!!!\n");
        return polynomialDegree(p.op(0) * ex_to<numeric>(p.op(1)).to_int(), considerPars);
      }
      if ( is_a<mul>(e) ){
        int d = 0;
        for ( const ex &op : e )
          d += polynomialDegree(op, considerPars);
        return d;
      }
      if ( is_a<add>(e) ){
        int d = 0;
        for ( const ex &op : e )
          d = max(d, polynomialDegree(op, considerPars));
        return d;
      }
      assertM(false, "Got strange expression type!!!! " << e << NL);
      return 0;
    }

    int varsDegree(const ex &e) const{
      return polynomialDegree(e, false);
    }
  protected:
    void makeFalse();
    void variablesStr2set(std::string &str, Symbols &s);
    static unsigned counter;
    const unsigned _id;
};

std::ostream &operator<<(std::ostream &out, const Conjunction &c);

#endif //_CONJUNCTION_HPP_
