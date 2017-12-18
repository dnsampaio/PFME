#include <fstream>
#include "Disjunction.hpp"

using namespace std;

typedef unsigned char uchar;
#ifndef DO_SCHWEIGHOFER_TESTER

int main(int argc, char *argv[]){
  Disjunction sys;
  bool cPrint = false;
  int startFrom = 1;
  if ( argc != 1 and (!strcmp("-c", argv[1]) ) ){
    cPrint = true;
    startFrom = 2;
  }
  if ( startFrom == argc ){
    cerr << "Reading from console / stdin\n\n";
    sys.read(cin);
  }
  else if ( argv[startFrom][0] == '[' ){
    stringstream s;
    for (; startFrom < argc; startFrom++ )
    s << argv[startFrom];

    sys.read(s);
  }
  else{
    for (; startFrom < argc; startFrom++ ){
      ifstream f(argv[startFrom], ifstream::in);
      if ( !f.is_open() and f.good() ){
        cerr << "Don't know what to do with argument " << argv[startFrom] << '\n';
        continue;
      }
      if ( f.is_open() and f.good() ){
        Disjunction sub(f);
        sys.join(sub);
      }
    }
  }
  sys.eliminateVariables();
  sys.simplifyFactor();
  sys.removeImplicators();
  DEBUG(1, "End system is:\n" << sys << NL);
  if ( cPrint ){
    sys.c_print(cout);
  }
  else{
    cout << sys << NL;
  }
  return 0;
}
#else
#include <cmath>
#include "Schweighofer.hpp"

typedef sysType::const_iterator ci;
typedef std::pair<ex, unsigned> cst;

void pp(const sysType &s, const unsigned &c){
  if ( c == 0 || s.empty() )
    return;

  cout << "System {\n";
  unsigned space = 1 + floor(log10((double) ( c )));
  for ( const cst &e : s )
    cout << '\t' << '[' << setw(space) << e.second << "] " << e.first << GE << 0 << NL;
  cout << "}\n";
}

int main(int argc, char *argv[]){
  sysType sys;
  unsigned c = 0;
  if ( argc == 2 ){
    ifstream f(argv[1], ifstream::in);
    if ( !f.is_open() and f.good() ){
      cerr << "Don't know what to do with argument " << argv[1] << '\n';
      exit(1);
    }
    Disjunction dis(f);
    if ( dis.size() != 1 ){
      cerr << "Can't handle multiple systems\n";
      exit(1);
    }
    auto nsyst = dis.begin();
    for ( cc cst : nsyst->eqs ){
      ci it = sys.find(cst->exp);
      if ( it == sys.end() ){
        sys[cst->exp] = ++c;
      }
      it = sys.find(expand(-cst->exp));
      if ( it == sys.end() ){
        sys[expand(-cst->exp)] = ++c;
      }
    }
    for ( cc cst : nsyst->ineqs ){
      ci it = sys.find(cst->exp);
      if ( it == sys.end() ){
        sys[cst->exp] = ++c;
      }
    }
  }

  if ( sys.size() )
    pp(sys, c);

  GiNaC::parser p(Constraint::SymTab);
  unsigned degree = 2;
  SchweighoferTester *t = nullptr;
  bool do_print = true;
  while ( !cin.eof() ){
    if ( do_print ){
      cout << "Commands: (A)ppend one constraint; E(x)it;\n\t(P)rint system;(C)hange ST degree [current=" << degree << "];\n";
      if ( sys.size() )
        cout << "\t(T)est if an expression is implied;\n\t(D)elete one constraint; Obtaint (R)oot of the system;\n\t(S)how ST expressions; Show ST (m)onomials;\n";
    }
    do_print = true;
    fflush(stdin);
    string s;
    cin >> s;
    cout << "Command: " << s << '[';
    switch ( toupper(s[0]) ){
      case 'A': {
        cout << "Add constraint]\nEnter expression: ";
        fflush(stdin);
        cin >> s;
        fflush(stdin);
        cout << "Entered " << s << NL;
        ex e = p(s);
        ci it = sys.find(e);
        if ( it == sys.end() ){
          sys[e] = ++c;
          cout << "Added constraint [" << c << "] " << e << NL;
          pp(sys, c);
          if ( t != nullptr ){
            cout << "Erasing old tester\n";
            delete t;
            t = nullptr;
          }
          break;
        }
        cout << "Constraint [" << it->second << "] " << it->first << " is already in the system\n";
        break;
      }
      case 'P': {
        if ( sys.empty() ){
          do_print = false;
          continue;
        }
        cout << "Print]\n";
        pp(sys, c);
        break;
      }
      case 'T': {
        if ( !sys.size() ){
          do_print = false;
          break;
        }
        cout << "Test]\n";
        if ( t == nullptr ){
          cout << "Building tester with ";
          pp(sys, c);
          t = new SchweighoferTester(sys, degree);
        }
        assert(t != nullptr);
        cout << "Enter constraint to be tested: ";
        cin >> s;
        cout << s << NL;
        ex e = p(s);
        testResult tr = t->test(e, false);
        cout << tr << NL;
        if ( tr.sign != SIGN::UNKNOWN )
          t->printResult(cout, true) << NL;
        break;
      }
      case 'D': {
        if ( sys.empty() ){
          do_print = false;
          continue;
        }
        pp(sys, c);
        cout << "Delete constraint]\n";
        cout << "Enter number of constraint to delete: ";
        unsigned del;
        cin >> del;
        cout << del << NL;
        if ( del > c ){
          cout << del << " is not in the system\n";
          break;
        }
        bool found = false;
        for ( cst i : sys ){
          if ( i.second == del ){
            found = true;
            cout << '[' << del << "] " << i.first << " was removed from the system.\n";
            if ( 1 != sys.erase(i.first) )
		    assert(false);

            if ( t != nullptr ){
              cout << "Erasing old tester\n";
              delete t;
              t = nullptr;
            }
            break;
          }
        }
        if ( !found )
          cout << del << " is not in the system\n";
        break;
      }
      case 'R': {
        if ( sys.empty() ){
          do_print = false;
          continue;
        }
        cout << "Find roots]\n";
        map<int, sysType> constraintsBySize;
        int maxSize = 0, minSize = 99999999;
        for ( auto c : sys ){
          int sz = c.first.nops();
          maxSize = max(maxSize, sz);
          minSize = min(minSize, sz);

          constraintsBySize[sz].insert(c);
        }

        sysType newSys = constraintsBySize[minSize];
        SchweighoferTester *nt = new SchweighoferTester(newSys, degree);

        int removed = 0;
        while ( minSize < maxSize ){
          minSize++;
          if ( constraintsBySize.find(minSize) == constraintsBySize.end() )
            continue;
          for ( const auto &nc : constraintsBySize[minSize] ){
            testResult tr = nt->test(nc.first, false);
            DEBUG(7, "The expression " << nc.first << " is " << tr << NL);
            switch ( tr.sign ){
              case SIGN::ABSURD: {
                sys.clear();
                delete nt;
                delete t;
                cout << "The system is empty!\n";
                goto quitReducing;
              }
              break;
              case SIGN::GEZ:
              case SIGN::GTZ:
              case SIGN::ZERO: {
                removed++;
                DEBUG(7, "Remove the constraint " << nc.first << " as it is implied to be " << tr << NL);
                continue;
              }
              default: {
                DEBUG(7, "The constraint " << c << " is not implied " << tr << " by the remaining constraints\n");
                newSys.insert(nc);
                delete nt;
                nt = new SchweighoferTester(newSys, degree);
              }
            }
          }
        }
        if ( removed ){
          swap(newSys, sys);
          if ( t )
            delete t;
          t = nt;
          nt = nullptr;
          cout << "Removed " << removed << " redundant constraints.\nThe system is now:\n";
          pp(sys, c);
        }
        quitReducing: break;
      }
      case 'C':
        cout << "Change degree]\nCurrent degree is " << degree << "\nEnter a new degree: ";
        unsigned newDegree;
        cin >> newDegree;
        if ( newDegree != degree ){
          delete t;
          t = nullptr;
          degree = newDegree;
          cout << "Changed degree to " << degree << NL;
        }
        break;
        case 'S':{
          if ( sys.empty() ){
            do_print = false;
            continue;
          }
          if ( t == nullptr ){
            cout << "Building tester with ";
            pp(sys, c);
            exset sysExs;
            for ( const cst &it : sys )
            sysExs.insert(it.first);
            t = new SchweighoferTester(sysExs, degree);
          }
          assert(t);
          const auto m = t->getIneqs();
          for ( const auto &e : m )
          cout << '[' << e.second << "] " << e.first << GE << 0 << NL;
        }
        break;
        case 'M':{
          if ( sys.empty() ){
            do_print = false;
            continue;
          }
          cout << "Print monomials]\n";
          if ( t == nullptr ){
            cout << "Building tester with ";
            pp(sys, c);
            exset sysExs;
            for ( const cst &it : sys )
            sysExs.insert(it.first);
            t = new SchweighoferTester(sysExs, degree);
          }
          assert(t);
          const auto m = t->getMonomials();
          for ( const auto &e : m )
          cout << '[' << e.second << "] " << e.first << GE << 0 << NL;
        }
        break;
        case 'X':
        goto end;

        default:{
          cout << "!!] : Bad command!!!\nTry again.\n";
          break;
        }

      }
    }
  end: sys.clear();
  if ( t != nullptr )
    delete t;
  t = nullptr;
  cout << "Bye :p]\n";
  return 0;
}
#endif
