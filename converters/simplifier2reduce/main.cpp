#ifdef SERVER_V
#ifndef NDEBUG
#define NDEBUG
#endif
#endif
#ifndef DEB_LVL
#define DEB_LVL 3
#define UNDO_DEB_MAIN_CPP_
#endif

#include "Conjunction.hpp"

#include <ginac/ginac.h>

#include <iostream>
#include <fstream>
#include <sstream>
#include <utility>

using namespace std;

typedef unsigned char uchar;
class Disjunction;
ostream &operator<<(ostream &out, const Disjunction& s);
class Disjunction
{
  public:
    typedef Conjunction Conj;
    typedef list<Conjunction> Conjs;
    typedef Conjs::iterator iterator;
    typedef Conjs::const_iterator citerator;

    void join(const Conjs & cjs){
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

    void join(const Disjunction & other){
      join(other.conjs);
    }

    Disjunction(){
    }

    Disjunction(istream &in){
      read(in);
      if ( conjs.empty() )
        conjs.push_back(Conjunction::obvious);
    }

    void read(istream &in){
      stringstream ss;
      while ( not in.eof() ){
        string line;
        getline(in, line);
        for ( const char c : line ){
          if ( c == ' ' or c == '\t' or c == '\n' or c == '\r' )
            continue;
          ss << c;
        }
      }
      string buff = ss.str();

      ss.clear();
      for ( size_t s = buff.find_last_of(';'); s != string::npos; s = buff.find_last_of(';') ){
        string o = buff.substr(s + 1);
        buff.erase(s);
        if ( o.size() > 3 ){
          Conj nc(o);
          for ( const Conj &c : conjs )
            if ( nc == c )
              continue;
          conjs.push_front(nc);
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

    void eliminateAbsurds(){
      for ( auto it = conjs.begin(); it != conjs.end(); ){
        if ( it->hasInverseConstraints() ){
          if ( conjs.size() == 1 ){
            *it = Conjunction::absurd;
            return;
          }
          else it = conjs.erase(it);
        }
        else it++;
      }
    }

    void removeDuplicates(){
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

    ostream &print(ostream &out) const{
      string bef = "rlset r$\non fort;\nfort_width := 999999999;\n";
      for ( const Conj &c : conjs ){
        out << bef << c;
        bef = "\n";
      }
      return out;
    }

  private:
    Conjs conjs;
};

ostream &operator<<(ostream &out, const Disjunction& s){
  return s.print(out);
}

int main(int argc, char *argv[]){

  srand(0);
  Disjunction sys;
  bool files = false, strings = false;
  for ( int i = 1; i < argc; i++ ){

    ifstream f(argv[i], ifstream::in);
    if ( f.is_open() and f.good() ){
      Disjunction sub(f);
      sys.join(sub);
      files = true;
    }
    else{
      if ( argv[i][0] == '[' ){
        stringstream s;
        s << argv[i];
        Disjunction sub(s);
        sys.join(sub);
        strings = true;
      }
    }
  }
  if ( not ( files || strings ) ){
    sys.read(cin);
  }
  sys.eliminateAbsurds();

  cout << sys << '\n';
  return 0;
}

#ifdef UNDO_DEB_MAIN_CPP_
#undef UNDO_DEB_MAIN_CPP_
#undef DEB_LVL
#endif
