#include <isatbmc.hh>

ISATBMCFalsification::ISATBMCFalsification(IModel& model)
  : SATBMCFalsification(model)
{
  logger << "Creating ISATBMC algorithm instance "
         << get_param("alg_name") << " @" << this
         << endl;
}

ISATBMCFalsification::~ISATBMCFalsification()
{
  logger << "Destroying ISATBMC algorithm instance"
         << get_param("alg_name") << " @" << this
         << endl;
}
