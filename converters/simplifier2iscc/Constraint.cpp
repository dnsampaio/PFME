#include "Constraint.hpp"

#include <ginac/ginac.h>

#include <cassert>
#include <iostream>
#include <sstream>

using namespace std;
using namespace GiNaC;

Constraint::cc Constraint::get(const int id){
  if ( id == trueC.id )
    return &trueC;
  if ( id == falseC.id )
    return &falseC;
  return &( constraints.find(id)->second );
}

Constraint::cc Constraint::get(const ex &expr, bool isEq){
  if ( obvious(expr, isEq) )
    return &trueC;

  if ( absurd(expr, isEq) )
    return &falseC;

  ex x = expand(expr);

  if ( x.nops() > 1 ){

    ex g = *x.begin();

    for ( const ex &o : x ){
      g = gcd(g, o);
    }

    if ( is_a<numeric>(g) )
      x = expand(x / g);
  }

  if ( isEq and is_a<mul>(x) ){
    const ex minX = expand(-x);
    if ( ( not is_a<mul>(minX) ) or ( minX.nops() < x.nops() ) )
      x = minX;
  }

  const ex exp = x;

  if ( is_a<numeric>(exp) ){
    if ( ex_to<numeric>(exp).is_negative() )
      return ( &falseC );

    if ( not isEq )
      return &trueC;

    if ( ex_to<numeric>(exp).is_zero() )
      return &trueC;

    return &falseC;
  }

  for ( auto const &ct : constraints ){
    const Constraint &c = ct.second;
    if ( ( isEq == c.eq ) and ( ( c.exp.is_equal(exp) ) or ( isEq and ( c.exp.is_equal(-exp) ) ) ) ){
      return &c;
    }
  }

  int id = nId++;
  //Always create the negation
  if ( not isEq ){
    constraints.insert({-id, {-exp - 1, -id, false}});
  }
  return &constraints.insert({id, {exp, id, isEq}}).first->second;
}

Constraint::cc Constraint::get(const std::string &buf){
  parser prsr(SymTab);
  ex x;
  if ( buf.empty() or isTrue(buf) )
    return &Constraint::trueC;

  if ( isFalse(buf) )
    return &Constraint::falseC;

  bool isEq = false;
  if ( buf.substr(0, 2) == "eq" ){
    isEq = true;
    x = prsr(buf.substr(2));
  }
  else if ( buf.substr(0, 4) == "ineq" ){
    x = prsr(buf.substr(4));
  }
  else{
    size_t pos;
    if ( ( pos = buf.find('>') ) != string::npos ){
      x = prsr(buf.substr(0, pos));
      if ( buf[pos + 1] == '=' )
        x -= prsr(buf.substr(pos + 2));
      else x -= 1 + prsr(buf.substr(pos + 1));
    }
    else if ( ( pos = buf.find('<') ) != string::npos ){
      x = prsr(buf.substr(0, pos));
      if ( buf[pos + 1] == '=' )
        x = prsr(buf.substr(pos + 2)) - x;
      else x = prsr(buf.substr(pos + 1)) - x - 1;
    }
    else if ( ( pos = buf.find("==") ) != string::npos ){
      x = prsr(buf.substr(0, pos)) - prsr(buf.substr(pos + 2));
      isEq = true;
    }
    else{
      exit(BAD_INPUT);
    }
  }
  return get(x, isEq);
}

void Constraint::addSymbol(const string &s){
  symbol sy(s);
  if ( SymTab.insert({s, sy}).second ){
    symbols.append(sy);
    return;
  }
  for ( const ex &c : symbols )
    if ( sy == c ){
      return;
    }
  symbols.append(sy);
}

bool Constraint::obvious(const ex &exp, bool eq){
  if ( eq )
    return is_a<numeric>(exp) and ex_to<numeric>(exp).is_zero();
  else return is_a<numeric>(exp) and !ex_to<numeric>(exp).is_negative();
}

bool Constraint::absurd(const ex &exp, bool eq){
  if ( eq )
    return is_a<numeric>(exp) and !ex_to<numeric>(exp).is_zero();
  else return is_a<numeric>(exp) and ex_to<numeric>(exp).is_negative();
}

Constraint::Constraint(const ex &d, const int oid, const bool e) :
    exp(d), eq(e), id(oid){
}

Constraint::Constraint(bool t) :
    exp(( t ) ? 0 : -1), eq(false), id(( t ) ? 1 : -1){
}

bool Constraint::isTrue(const std::string &s){
  if ( s.size() != 4 )
    return false;
  static const string t1 = "true", t2 = "TRUE";

  for ( unsigned i = 0; i < 4; i++ ){
    if ( ( s[i] != t1[i] ) and ( s[i] != t2[i] ) )
      return false;
  }

  return true;
}
bool Constraint::isFalse(const std::string &s){
  static const string f1 = "false", f2 = "FALSE";
  if ( s.size() != 5 )
    return false;

  for ( unsigned i = 0; i < 5; i++ ){
    if ( ( s[i] != f1[i] ) and ( s[i] != f2[i] ) )
      return false;
  }

  return true;
}

ostream &Constraint::print(ostream &out) const{
  if ( id == trueC.id )
    return out << "true";

  if ( id == falseC.id )
    return out << "false";

  out << exp;
  if ( eq )
    return out;

  return ( out << " >= 0" );
}

ostream &Constraint::c_print_recurse(ostream &out, ex op) const{
  string front = "";

  if ( is_a<add>(op) ){
    for ( const ex &sub : op ){
      if ( is_a<numeric>(sub) ){
        if ( sub < 0 )
          out << sub;
        else
          out << front << sub;
      } else {
        out << front;
        c_print_recurse(out, sub);
      }
      front = "+";
    }
    return out;
  }
  if ( is_a<mul>(op) ){
    for ( const ex &sub : op ){
      if ( is_a<symbol>(sub) || ( is_a<numeric>(sub) and (sub >= 0) ) ){
//        if ( is_a<symbol>(sub)){
          out << front << sub;
//        } else {
//          out << front << sub;
//        }
      } else {
        out << front;// << '(';
        c_print_recurse(out, sub);// << ')';
      }
      front = "*";
    }
    return out;
  }

  if ( is_a<power>(op)){
    if ( is_a<numeric>(op.op(1)) and ex_to<numeric>(op.op(1)).is_integer() ){
      int c = ex_to<numeric>(op.op(1)).to_int();
      if ( c == 0 )
        return out;

      stringstream op0;
      c_print_recurse(op0, op.op(0));
      if( c < 0 ){
        out << "1/(";
        c = -c;
      }
      c--;
      out << '(' << op0.str();
      while ( c-- > 0 )
        out << "*" << op0.str();
      out << ')';
      if ( op.op(1) < 0 )
        out << ')';
      return out;
    }

    out << "pow(";
    c_print_recurse(out, op.op(0));
    out << ',';
    c_print_recurse(out, op.op(1));
    return out << ')';
  }
  if (is_a<numeric>(op) ){
    if ( op < 0 )
      return out << "(" << op << ")";
    return out << op;
  }
  return out << op ;
}

ostream &Constraint::c_print(ostream &out) const{
  if ( id == trueC.id )
    return out << 1;

  if ( id == falseC.id )
    return out << 0;

  char oper1 = '>';
  if ( eq )
    oper1 = '=';

  if ( is_a<symbol>(exp) or (is_a<numeric>(exp) ) ){
//    if ( is_a<symbol>(exp) )
//      return out << "((long)(" << exp << "))" << oper1 << "=0";
    return out << exp << oper1 << "=0";
  }
  /* test for -n >= 0 */
  ex inv = expand (-exp);

  if ( is_a<symbol>(inv) )
    return out << "0" << oper1 << "=(" << inv << ")";

  /* test for -f(n)  >= 0 */
  if ( inv.nops() < exp.nops() ){
    out << "0" << oper1 << '=';
    return c_print_recurse(out, inv);
  }

  /* Convert e1 - e2 + e3 - e4 + c >= 0  ==============>  e1 - e2 + e3 - e4 >= -c */

  ex rhsExp = 0;
  ex lhsExp = factor(exp, factor_options::all);
  if ( is_a<add>(lhsExp) ){
    for ( ex op : lhsExp ){
      if ( is_a<numeric>(op) ){
        numeric tmpOp = ex_to<numeric>(op);
        ex tmpLhs = factor(expand(lhsExp - tmpOp), factor_options::all);
        rhsExp = -tmpOp;
        lhsExp = tmpLhs;
        break;
      }
    }
  }
  /* Convert e1 - e2 + e3 - e4 >= -c  ==============>  e1  + e3 >= e2 +e4 -c */
testLHS:
  if ( is_a<add>(lhsExp)){
    for ( ex op : lhsExp ){
      ex invOp = expand(-op);
      if ( invOp.nops() < op.nops() ){
        rhsExp += invOp;
        lhsExp = factor(expand(lhsExp + invOp), factor_options::all);
        goto testLHS;
      }
      if ( is_a<mul>(op) ){
        for ( ex subOp : op ){
          if ( is_a<numeric>(subOp) and ( subOp < 0 ) ){
            rhsExp -= op;
            lhsExp = factor(expand(lhsExp - op), factor_options::all);
            goto testLHS;
          }
        }
      }
    }
  }
  stringstream lhsS, rhsS;
  c_print_recurse(lhsS, lhsExp);
  c_print_recurse(rhsS, rhsExp);
  return out << lhsS.str() << oper1 << "="  << rhsS.str();
}

map<int, Constraint> Constraint::constraints;
symtab Constraint::SymTab;
lst Constraint::symbols;
const Constraint Constraint::trueC(true);
const Constraint Constraint::falseC(false);
int Constraint::nId = 2;
