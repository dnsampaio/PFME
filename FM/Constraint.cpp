#include "Constraint.hpp"

#include <ginac/ginac.h>

#include <cassert>
#include <iostream>
#include <sstream>
#include "Schweighofer.hpp"
#include <cmath>

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

	bool r = divide(x, x.integer_content(), x);
	if ( ! r ){
		assert(false);
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

Constraint::cc Constraint::get(std::string buf){
  SIGN op = SIGN::UNKNOWN;
	parser prsr(SymTab);
	ex x;
	if ( buf.empty() or isTrue(buf) )
		return &Constraint::trueC;

	if ( isFalse(buf) )
		return &Constraint::falseC;

	if ( buf.substr(0, 2) == "eq" ){
	  op = SIGN::ZERO;
		x = prsr(buf.substr(2));
	}
	else if ( buf.substr(0, 4) == "ineq" ){
	  op = SIGN::GEZ;
		x = prsr(buf.substr(4));
	}
	else{
		size_t pos = buf.find_first_of("><=");
		assertM(pos != string::npos, "Don't know what to do with:" << buf << NL);
		bool two_chars = false;

    switch ((int) buf[pos]){
      case '>':{
        if ( buf[pos+1] == '='){
          op = SIGN::GEZ;
          two_chars = true;
        } else
          op = SIGN::GTZ;
        break;
      }
      case '<':{
        if ( buf[pos+1] == '='){
          op = SIGN::LEZ;
          two_chars = true;
        } else
          op = SIGN::LTZ;
        break;
      }
      case '=':{
        op = SIGN::ZERO;
        two_chars = ( buf[pos+1] == '=');
        break;
      }
    }
    string rhsStr = (two_chars?buf.substr(pos+2):buf.substr(pos+1));
    string lhsStr = buf.substr(0, pos);

    DEBUG(10, "LHS:" << lhsStr << "\nOpperand: " << op << "\nRHS:" << rhsStr << NL);
    ex rhs, lhs;
    try{
      rhs = prsr(rhsStr);
    } catch (const GiNaC::parse_error& e) {
      cerr << "Error parsing constraint: " << buf << "\n\tat the RHS expression:" << rhsStr << "\n\t" << e.what();
      exit(BAD_INPUT);
    }
    try{
      lhs = prsr(lhsStr);
    } catch (const GiNaC::parse_error& e) {
      cerr << "Error parsing constraint: " << buf << "\n\tat the LHS expression:" << lhsStr << "\n\t" << e.what();
      exit(BAD_INPUT);
    }

    switch (op){
      case SIGN::ABSURD:
      case SIGN::UNKNOWN:{
        cerr << "Something went wrong when generating constraint from string " << buf << NL << rhs << op << lhs << NL;
        exit(BAD_INPUT);
      }
      case SIGN::GEZ:{
        x = expand(lhs - rhs);
        break;
      }
      case SIGN::LEZ:{
        x = expand(rhs - lhs);
        break;
      }
      case SIGN::ZERO:{
        x = expand(lhs - rhs);
        break;
      }
      case SIGN::GTZ:{
        x = expand(lhs - rhs -1);
       break;
      }
      case SIGN::LTZ:{
        x = expand(rhs - lhs -1);
        break;
      }
    }
	}
	return get(x, (op == SIGN::ZERO));
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

	static std::streambuf const * cerrbuf = std::cerr.rdbuf();

	if ( cerrbuf == out.rdbuf() )
	  return ( out << '[' <<setw(2+(int)(floor(log10(nId))))<< id << "] " << exp << ( ( eq ) ? ( ( id < 0 ) ? NE : " = " ) : GE ) << "0" );
	return ( out << exp << ' ' << ( ( eq ) ? ( ( id < 0 ) ? '!' : '=' ) : '>' ) << "= 0" );
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
	if ( id == trueC.id ){
		DEBUG(10, exp << " --- becomes ---->" << 1 << NL);
		return out << 1;
	}

	if ( id == falseC.id ){
		DEBUG(10, exp << " --- becomes ---->" <<0 << NL);
		return out << 0;
	}

	char oper1 = '>';
	if ( eq )
		oper1 = '=';

	if ( is_a<symbol>(exp) or (is_a<numeric>(exp) ) ){
		DEBUG(10, exp << " --- becomes ---->" << exp << oper1 << "=0" << NL);
		return out << exp << oper1 << "=0";
	}
	/* test for -n >= 0 */
	ex inv = expand (-exp);

	if ( is_a<symbol>(inv) ){
		DEBUG(10, exp << " --- becomes ---->" << "0" << oper1 << "=(" << inv << ")" << NL);
		return out << "0" << oper1 << "=(" << inv << ")";
	}

	/* test for -f(n)  >= 0 */
	if ( inv.nops() < exp.nops() ){
		stringstream ss;
		ss << "0" << oper1 << '=';
		c_print_recurse(ss, inv);
		DEBUG(10, exp << " --- becomes ---->" << ss.str() << NL);
		return out << ss.str();
		//    out << "0" << oper1 << '=';
		//    return c_print_recurse(out, inv);
	}

	/* Convert e1 - e2 + e3 - e4 + c >= 0  ==============>  e1 - e2 + e3 - e4 >= -c */

	ex rhsExp = 0;
	ex lhsExp = expand(exp);
	if ( is_a<add>(lhsExp) ){
		DEBUG(10, lhsExp << " is an add expression\n");
		for ( const ex &op : lhsExp ){
			DEBUG(10, op << " is a operand\n");
			if ( is_a<numeric>(op) and ( op < 0) ){
				rhsExp -= op;
				DEBUG(10, op << " is a negative number operand, adding inverse to rhsExp becoming: " << rhsExp << NL);
				continue;
			}
			if ( is_a<mul>(op) ){
				DEBUG(10, op << " is a mul operand\n");
				bool invert = false;
				for ( const ex &subOp : op ){
					DEBUG(10, subOp << " is a sub-operand\n");
					if ( is_a<numeric>(subOp) and ( subOp < 0 ) ){
						DEBUG(10, subOp << " is a negative number, inverting invert\n");
						invert = !invert;
					}
				}
				if (invert){
					rhsExp -= op;
					DEBUG(10, op << " is a negative multiplied operand, such that rhsExp becomes: " << rhsExp << NL);
				} else {
					DEBUG(10, op << " is NOT a negative multiplied operand, such that rhsExp becomes: " << rhsExp << NL);
				}
				continue;
			}
			DEBUG(10, "Operand " << op << " is nor a numeric value nor a mul\n");
		}
	}

	lhsExp = expand(lhsExp + rhsExp);

	DEBUG(10, exp << " --- becomes ---->" << lhsExp << " <= " << rhsExp << NL);

	stringstream lhsS, rhsS;
	c_print_recurse(lhsS, factor(lhsExp));
	c_print_recurse(rhsS, factor(rhsExp));
	DEBUG(10, exp << " ------------- becomes ---->" << lhsS.str() << oper1 << "="  << rhsS.str() << NL);
	return out << lhsS.str() << oper1 << "="  << rhsS.str();
}

map<int, Constraint> Constraint::constraints;
symtab Constraint::SymTab;
lst Constraint::symbols;
const Constraint Constraint::trueC(true);
const Constraint Constraint::falseC(false);
int Constraint::nId = 2;
