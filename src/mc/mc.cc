#include <mc.hh>

MCAlgorithm::MCAlgorithm(IModel& model)
  : f_mm(ModelMgr::INSTANCE())
  , f_em(ExprMgr::INSTANCE())
  , f_tm(TypeMgr::INSTANCE())
  , f_model(model)
  , f_traces()
{
  logger << "Creating MC algoritm instance "
         << get_param("alg_name")
         << " @" << this
         << endl;
}

MCAlgorithm::~MCAlgorithm()
{
  logger << "Destroying MC algoritm instance"
         << get_param("alg_name")
         << " @" << this
         << endl;
}

void MCAlgorithm::set_param(string key, Variant value)
{ f_params [ key ] = value; }

Variant& MCAlgorithm::get_param(const string key)
{
  const ParametersMap::iterator eye = f_params.find(key);

  if (eye != f_params.end()) {
    return (*eye).second;
  }

  else return NilValue;
}
