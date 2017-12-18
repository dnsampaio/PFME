#pragma once
#ifndef __CONSTRAINT_HPP_
#define __CONSTRAINT_HPP_
#include <ginac/ginac.h>
#include <map>
#include <iostream>
#include <sstream>

const int BAD_INPUT = 1;

class Constraint{
  public:
    const GiNaC::ex exp;
    bool eq;
    typedef const Constraint * cc;
    typedef const GiNaC::ex cs;

    static cc get(const int id);
    static cc getFalse(){
      return &falseC;
    }
    static cc getTrue(){
      return &trueC;
    }
    static cs getOrInsertSymbol(const std::string &s){
      if ( s.length() == 0)
        return GiNaC::ex(0);

      GiNaC::symtab::const_iterator sy = SymTab.find(s);
      if ( sy == SymTab.end() ){
        SymTab[s] = GiNaC::symbol(s);
        return SymTab[s];
      }
      return sy->second;
    }
    static cc get(const std::string &buf);
    static cc get(const GiNaC::ex &expr, bool isEq = false);
    static void addSymbol(const std::string &s);

    const static Constraint trueC, falseC;

    std::ostream &print(std::ostream &out) const;
    std::ostream &c_print(std::ostream &out) const;

    const Constraint *getNot() const{
      return get(-id);
    }

    bool hasAny(const GiNaC::lst &list ) const {
      for ( const GiNaC::ex &e : list ){
        if ( GiNaC::quo(exp, e, e).is_zero() )
          continue;
        return true;
      }
      return false;
    }

    const int id;
    static GiNaC::symtab SymTab;
    static GiNaC::lst symbols;

  private:
    static int nId;
    static std::map<int, Constraint> constraints;
    static bool obvious(const GiNaC::ex &exp, bool eq);
    static bool absurd(const GiNaC::ex &exp, bool eq);

    Constraint(const GiNaC::ex &d, const int oid, const bool e = false);
    Constraint(bool trueC);
    std::ostream &c_print_recurse(std::ostream &out, GiNaC::ex op) const;

    static bool isTrue(const std::string &s);
    static bool isFalse(const std::string &s);
};

template<class T> T&operator<<(T &out, Constraint::cc c){
  return c->print(out);
}

typedef GiNaC::lst Symbols;
typedef const Constraint * cc;
typedef std::set<cc> Constraints;

#endif//__CONSTRAINT_HPP_

