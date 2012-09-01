#include <isatbmc.hh>

ISATBMCFalsification::ISATBMCFalsification(IModel& model)
  : SATBMCFalsification(model)
{
  trace << "Creating ISATBMC algorithm instance "
        << get_param("alg_name") << " @" << this
        << endl;
}

ISATBMCFalsification::~ISATBMCFalsification()
{
  trace << "Destroying ISATBMC algorithm instance"
        << get_param("alg_name") << " @" << this
        << endl;
}
