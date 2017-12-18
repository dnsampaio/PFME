#ifndef NDEBUG
#include "debug.hpp"
#include <ctype.h>
#include <sstream>
DEB_INF DI;
#else
#ifdef INTERACTIVE_MODE
#include "debug.hpp"
DEB_INF DI;
#endif
#endif

#include <string>
using namespace std;
bool getResponse(const string question, const bool def){
  (void)(question);

#ifdef INTERACTIVE_MODE
  cout.flush();
  cerr.flush();
  string answer;
  cout << question << endl << "(Y/N)? [default = " << ( ( def ) ? 'y' : 'n' ) << "]";
  getline(cin, answer);

  if ( ( answer.size() < 1 ) or ( answer.size() > 1 ) )
    return def;

  char r = toupper(answer.at(0));

  if ( r == 'Y' )
    return true;
  if ( r == 'N' )
    return false;
  return def;
#else
    return def;
#endif
}
