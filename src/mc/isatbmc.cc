#include <isatbmc.hh>

ISATBMCFalsification::ISATBMCFalsification(IModel& model)
  : SATBMCFalsification(model)
{
  TRACE << "Creating ISATBMC algorithm instance "
        << get_param("alg_name") << " @" << this
        << endl;
}

ISATBMCFalsification::~ISATBMCFalsification()
{
  TRACE << "Destroying ISATBMC algorithm instance"
        << get_param("alg_name") << " @" << this
        << endl;
}
