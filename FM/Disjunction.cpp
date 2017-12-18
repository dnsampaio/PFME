#include "Simplifier.hpp"
#include "Disjunction.hpp"
#include "debug.hpp"

using namespace std;

void Disjunction::join(const Conjs & cjs){
  for ( const Conjunction &oc : cjs ){
    bool insert = true;
    for ( const Conjunction &c : conjs ){
      if ( c == oc ){
        insert = false;
        break;
      }
    }
    if ( insert )
      conjs.push_back(oc);
  }
}

void Disjunction::join(const Disjunction & other){
  join(other.conjs);
}

void Disjunction::removeImplicators(){
  if ( conjs.size() < 2 )
    return;

  iterator end = conjs.end();
  for ( iterator i1 = conjs.begin(); i1 != end; ){
    for ( iterator i2 = next(i1); i2 != end; ){
      DEBUG(4, "Testing if\n" << *i2 << "\nimplies\n" << *i1 << NL);
      if ( i2->implies(*i1) ){
        DEBUG(4, "Yes it implies, removing the first one\n");
        i2 = conjs.erase(i2);
        continue;
      }
      DEBUG(4, "Testing the other way\n");
      if ( i1->implies(*i2) ){
        DEBUG(4, "Yes it implies, removing the second one\n");
        i1 = conjs.erase(i1);
        i2 = next(i1);
        continue;
      }
      i2++;
    }
    i1++;
  }
}

Disjunction::Disjunction(){
}

Disjunction::Disjunction(istream &in){
  read(in);
  if ( conjs.empty() )
    conjs.push_back(Conjunction::obvious);
}

void Disjunction::read(istream &in){
  stringstream ss;
  string line;
  for ( ; !in.eof(); in >> line ){
    DEBUG(9, "Got line: " << line << NL);
    for ( const char c : line ){
      if ( c == ' ' or c == '\t' or c == '\n' or c == '\r' )
        continue;
      ss << c;
    }
    line.clear();
  }
  string buff = ss.str();
  DEBUG(9, "Buffer string " << buff << NL);

  ss.clear();

  for ( size_t s = buff.find_first_of(';'); s != string::npos; s = buff.find_first_of(';') ){
    string newConj = buff.substr(0, s);
    buff = buff.substr(s + 1);
    DEBUG(10, "Buffer string:" << buff << NL);
    DEBUG(10, "Build conjunction with: " << newConj << NL);
    if ( newConj.size() > 3 ){
      DEBUG(9, "Build new conjunction\n");
      Conj nc(newConj);
      for ( const Conj &c : conjs )
        if ( nc == c )
          continue;
      conjs.push_back(nc);
    }
  }

  if ( buff.size() > 3 ){
    Conj nc(buff);
    for ( const Conj &c : conjs )
      if ( nc == c )
        continue;
    conjs.push_front(nc);
  }
}

void Disjunction::simplifyFactor(){
  removeDuplicates();
}

void Disjunction::removeDuplicates(){
  for ( iterator i = conjs.begin(); i != conjs.end(); ){
    if ( *i == Conjunction::obvious ){
      conjs.clear();
      conjs.push_back(Conjunction::obvious);
      return;
    }

    if ( *i == Conjunction::absurd ){
      if ( conjs.size() > 1 )
        i = conjs.erase(i);
      else i++;
      continue;
    }
    bool inc = true;
    for ( iterator ni = next(i); ni != conjs.end(); ni++ ){
      if ( *i == *ni ){
        iterator tmp = next(i);
        conjs.erase(i);
        i = tmp;
        inc = false;
      }
    }
    if ( inc )
      i++;
  }
}

void Disjunction::eliminateVariables(){
  for ( Conjs::iterator c = conjs.begin(); c != conjs.end(); ){
    if ( c->hasVariables() ){
      Conjunction nc = *c;
      conjs.remove(*c);
      DEBUG(4, "Removing variables from the conjunction: " << nc << NL);
      Simplifier s(nc);
      s.run();
      conjs.splice(conjs.end(), s.get());
      c = conjs.begin();
    } else
      c++;
  }
}

ostream &Disjunction::print(ostream &out) const{
  string bef = "";
  for ( const Conj &c : conjs ){
    out << bef << c;
    bef = "\n";
  }
  return out;
}

ostream &Disjunction::c_print(ostream &out) const{
  Symbols symbs;
  stringstream outs;
  string bef = "if ( (";
  for ( const Conj &c : conjs ){
    for ( const ex &s : c.pars )
      symbs.append(s);

    for ( const ex &s : c.vars )
      symbs.append(s);

    symbs.sort();
    symbs.unique();
    outs << bef;
    c.c_print(outs);
    bef = ") || (";
  }
  outs << ") )";
  return out << outs.str();
}

ostream &operator<<(ostream &out, const Disjunction& s){
  return s.print(out);
}
