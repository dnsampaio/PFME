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

int Conjunction::degree(const ex &e) {
  if ( is_a<numeric>(e) )
    return 0;
  if ( is_a<symbol>(e))
    return 1;
  if ( is_a<mul>(e) ){
    int d = 0;
    for ( const ex &op : e )
      d += degree(op);
    return d;
  }
  if ( is_a<add>(e) ){
    int d = 0;
    for ( const ex &op : e )
      d = std::max(d, degree(op));
    return d;
  }

  if ( is_a<power>(e) ){
    const power &pow = ex_to<power>(e);
    if ( !is_a<numeric>(pow.op(1)))
      throw 0;
    int pw = ex_to<numeric>(pow.op(1)).to_int();
    return degree(pow.op(0)) * pw;
  }
  throw 0;
  return -1000;
}

int Conjunction::degree(cc c) {
  if ( ! c )
    return 0;

  const ex e = expand(c->exp);
  return degree(e);
}

ostream &Conjunction::print(ostream& out) const{
  bool hasAffine = false, hasPolyn = false;
  if ( ( eqs.empty() && ineqs.empty() ) || ( obvious == *this ) )
    return out << "print True;";

  if ( absurd == *this )
    return out << "print False;";

  for ( cc c : eqs ){
    if ( is_a<numeric>(c->exp) && ( c->exp < 0 ) )
      return out << "print False;";
  }
  Symbols allvars = vars;
  for ( const ex &e : pars )
    allvars.append(e);

  Constraints peqs, pineqs, leqs, lineqs;

  for ( cc c : eqs ){
    if ( degree(c) > 1 ){
//      cerr << "peqs += " << c->exp << '\n';
      peqs.insert(c);
      hasPolyn = true;
    }
    else{
//      cerr << "leqs += " << c->exp << '\n';
      leqs.insert(c);
      hasAffine = true;
    }
  }

  for ( cc c : ineqs ){
    if ( degree(c) > 1 ){
//      cerr << "pineqs += " << c->exp << '\n';
      pineqs.insert(c);
      hasPolyn = true;
    }
    else{
//      cerr << "lineqs += " << c->exp << '\n';
      lineqs.insert(c);
      hasAffine = true;
    }
  }

  if ( !hasAffine ){ //We only have polynomials, isl/iscc can't help
    return out << "print True;";
  }
  //1: Write the linear part
  stringstream linearPart;
  string front = ":";
  for ( cc c : leqs ){
    linearPart << front << c << " = 0";
    front = " & ";
  }

  for ( cc c : lineqs ){
    linearPart << front << c << " >= 0";
    front = " & ";
  }
  linearPart << "};";
  string linear = linearPart.str();
  linearPart.clear();

  //2:Write parameters and variables string
  stringstream pvarsPart;
  pvarsPart << "[";
  front = "";
  for ( const ex &e : pars ){
    pvarsPart << front << e;
    front = ", ";
  }
  pvarsPart << "] -> {[";
  front = "";
  for ( const ex &e : vars ){
    pvarsPart << front << e;
    front = ", ";
  }
  pvarsPart << "]";

  string pvars = pvarsPart.str();
  pvarsPart.clear();

  //3: We test if the affine part is empty
  stringstream prefixSS;
  prefixSS << "S" << counter - _id;

  string prefix = prefixSS.str();
  prefixSS.clear();

  string postfix = ( hasPolyn ) ? "_AFFINE" : "";
  out << prefix << postfix << " := " << pvars << linear << '\n';
  out << "print \"card====\";\ncard(" << prefix << postfix << ");\n";

  if ( hasPolyn ){
    postfix = "_POL";
    int count = 1;
    for ( cc c : peqs ){ //If we have abc = 0, than we check either that lb(abc) > 0 or ub(abc) < 0
      out << prefix << postfix << count << " := " << pvars << " -> " << c->exp << ' ' << linear << '\n';
      out << "print \"lb====\";\nlb(" << prefix << postfix << count << ");\n";
      out << "print \"ub====\";\nub(" << prefix << postfix << count << ");\n";
      count++;
    }
    for ( cc c : pineqs ){ //If we have abc >= 0, than we check either that ub(abc) < 0
      out << prefix << postfix << count << " := " << pvars << " -> " << c->exp << ' ' << linear << '\n';
      out << "print \"ub====\";\nub(" << prefix << postfix << count << ");\n";
      count++;
    }
  }
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
