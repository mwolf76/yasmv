#include <satbmc.hh>

SATBMCAlgorithm::SATBMCAlgorithm(Model& model)
  : MCAlgorithm(model)
{
  logger << "Creating SATBMC algorithm instance "
         << get_param("alg_name") << " @" << this
         << endl;
}

SATBMCAlgorithm::~SATBMCAlgorithm()
{
  logger << "Destroying SATBMC algorithm instance"
         << get_param("alg_name") << " @" << this
         << endl;
}
