// Created on: Jun 20, 2015
// Author: Diogo N. SAMPAIO <dnsampaio@gmail.com>
//
//===-- /Simplifier/Conjunction.cpp - {Description} -------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// \brief
///
//===----------------------------------------------------------------------===//

#include "Conjunction.hpp"
#include <sstream>
#include <cmath>
/*
 #define NDEBUG
 #ifndef DEB_LVL
 #define DEB_LVL 0
 #define UNDO_DEB_CONJU_CPP_
 #endif
 */
#include <cmath>

using namespace std;
using namespace GiNaC;

int shrink_count_ugly = 0;

Conjunction Conjunction::obvious = Make(true);
Conjunction Conjunction::absurd = Make(false);
unsigned Conjunction::counter = 0;

Conjunction::Conjunction() :
    _id(counter++){
}

Conjunction Conjunction::Make(bool val){
  Conjunction c;
  if ( not val )
    c.eqs.insert(&Constraint::falseC);

  return c;
}

Conjunction::Conjunction(const Symbols &v, const Symbols &p, const Constraints &e, const Constraints &i, const unsigned id) :
    vars(v), pars(p), eqs(e), ineqs(i), _id(id){
  ineqs.erase(Constraint::getTrue());
  eqs.erase(Constraint::getTrue());
  if ( eqs.find(Constraint::getFalse()) != eqs.end() or ineqs.find(Constraint::getFalse()) != ineqs.end() ){
    *this = absurd;
    return;
  }
  else if ( eqs.empty() and ineqs.empty() ){
    *this = obvious;
    return;
  }
  else{
    removeUnused();
  }

  for ( cc c : ineqs ){
    if ( ineqs.find(c->getNot()) != ineqs.end() ){
      makeFalse();
      return;
    }
  }
  for ( cc c : ineqs ){
    if ( ineqs.find(c->getNot()) != ineqs.end() ){
      makeFalse();
      return;
    }
  }

  for ( auto it1 = ineqs.begin(); it1 != ineqs.end(); it1++ ){
    cc c = *it1;
    if ( ineqs.find(c->getNot()) != ineqs.end() ){
      makeFalse();
      return;
    }
  }
}

Conjunction::Conjunction(string &in) :
    _id(counter++){
  size_t s = in.find(':');
  if ( s == string::npos ){
    cerr << "Can't find conjunction start delimiter \":\"\n";
    exit(BAD_INPUT);
  }
  string conjStr = in.substr(s + 1);
  in.erase(s);
  s = in.find("->");
  string varsStr;
  if ( s == string::npos )
    varsStr = "[]";
  else{
    varsStr = in.substr(s + 2);
    in.erase(s);
  }

  if ( ( varsStr[0] != '[' ) or ( varsStr[varsStr.length() - 1] != ']' ) or ( in[0] != '[' ) or ( in[in.length() - 1] != ']' ) ){
    cerr << "No variables and no parameters to the conjunction\n";
    exit(BAD_INPUT);
  }

  varsStr = varsStr.erase(varsStr.length() - 1).substr(1);
  variablesStr2set(varsStr, vars);
  in = in.erase(in.length() - 1).substr(1);
  variablesStr2set(in, pars);

  for ( s = conjStr.find_last_of('&'); s != string::npos; s = conjStr.find_last_of('&') ){
    string o = conjStr.substr(s + 1);
    conjStr.erase(s);
    cc c = Constraint::get(o);
    if ( c == Constraint::getFalse() ){
      makeFalse();
      return;
    }
    if ( c == Constraint::getTrue() )
      continue;

    if ( c->eq )
      eqs.insert(c);
    else ineqs.insert(c);
  }
  {
    cc c = Constraint::get(conjStr);
    if ( c == Constraint::getFalse() ){
      makeFalse();
      return;
    }
    if ( c != Constraint::getTrue() ){
      if ( c->eq )
        eqs.insert(c);
      else ineqs.insert(c);
    }
  }

  detectEqs();
  if ( empty() ){
    *this = obvious;
    return;
  }

  removeUnused();
}

ostream &Conjunction::print(ostream& out) const{
  stringstream exEnd, exName;
  const unsigned ln = counter - _id;
  exName << "f" << ln;
  out << exName.str() << " := ";
  for ( const ex & s : vars ){
    exEnd << ')';
    out << "ex(" << s << ", ";
  }
  out << '(';
  exEnd << ')';
  if ( absurd == *this )
    out << "false";
  else if ( obvious == *this )
    out << "true";
  else{
    string front = "";
    for ( cc c : eqs ){
      out << front << c->exp << " = 0";
      front = " and ";
    }
    for ( cc c : ineqs ){
      out << front << c;
      front = " and ";
    }
  }
  out << exEnd.str() << ";\nrlqe " << exName.str() << ";\n";
  return out;
}

void Conjunction::insert(const string &constraint){
  if ( constraint.empty() )
    return;
  cc c = Constraint::get(constraint);
  if ( c->eq ){
    if ( c == Constraint::getFalse() ){
      makeFalse();
    }
    if ( c != Constraint::getTrue() )
      eqs.insert(c);
  }
  else{
    if ( ineqs.find(c->getNot()) != ineqs.end() ){
      makeFalse();
    }
    else ineqs.insert(c);
  }
}

void Conjunction::removeUnused(){
  removeUnused(pars);
  removeUnused(vars);
}

void Conjunction::removeUnused(Symbols &toSimplify){
  toSimplify.sort();
  toSimplify.unique();
  Symbols remaining;
  for ( const ex &e : toSimplify ){
    bool found = false;
    for ( cc c : eqs ){
      if ( quo(c->exp, e, e) != 0 ){
        remaining.append(e);
        found = true;
        break;
      }
    }
    if ( found )
      continue;
    for ( cc c : ineqs ){
      if ( quo(c->exp, e, e) != 0 ){
        remaining.append(e);
        found = true;
        break;
      }
    }
  }
  swap(toSimplify, remaining);
}

bool Conjunction::operator==(const Conjunction &other) const{
  return ( ( vars == other.vars ) and ( pars == other.pars ) and ( eqs == other.eqs ) and ( ineqs == other.ineqs ) );
}

bool Conjunction::hasVariables() const{
  return ( vars.nops() != 0 );
}

bool Conjunction::hasInverseConstraints() const{
  if ( *this == absurd )
    return true;

  if ( *this == obvious )
    return false;

  for ( cc c : ineqs )
    if ( ( c->id < 0 ) and ( ineqs.find(c->getNot()) != ineqs.end() ) )
      return true;
  return false;
}

bool Conjunction::empty() const{
  return ( eqs.empty() and ineqs.empty() );
}

bool Conjunction::hasEqs() const{
  if ( ( *this == absurd ) or ( *this == obvious ) )
    return false;
  return ( eqs.size() > 0 );
}

void Conjunction::makeFalse(){
  *this = Conjunction::absurd;
}

void Conjunction::variablesStr2set(string &str, Symbols &s){
  for ( size_t p = str.find_last_of(','); p != string::npos; p = str.find_last_of(',') ){
    string var = str.substr(p + 1);
    str.erase(p);
    if ( var.length() == 0 )
      continue;

    Constraint::cs symb = Constraint::getOrInsertSymbol(var);
    if ( not ( is_a<symbol>(symb) ) ){
      cerr << "Can't get symbol '" << var << "'\n";
      exit(BAD_INPUT);
    }
    s.append(symb);
  }
  if ( str.length() == 0 )
    return;

  Constraint::cs symb = Constraint::getOrInsertSymbol(str);
  if ( not ( is_a<symbol>(symb) ) ){
    cerr << "Can't get symbol '" << str << "'\n";
    exit(BAD_INPUT);
  }
  s.append(symb);
}

ostream &operator<<(ostream &out, const Conjunction &c){
  return c.print(out);
}

#ifdef UNDO_DEB_CONJU_CPP_
#undef UNDO_DEB_CONJU_CPP_
#undef DEB_LVL
#endif
