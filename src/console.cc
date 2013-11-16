/**
 * @file console.cc
 * @brief Command line options management
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 **/
#include <cstdio>
#include <iostream>
#include <console.hh>

using namespace axter;
using namespace std;

// static initialization
ConsoleMgr_ptr ConsoleMgr::f_instance = NULL;

ConsoleMgr::ConsoleMgr()
    : f_err( EZLOGGERVLSTREAM2(log_verbosity_not_set, cerr))
    , f_warn( EZLOGGERVLSTREAM2(log_always, cerr))
    , f_trace( EZLOGGERVLSTREAM2(log_often, cerr))
    , f_info( EZLOGGERVLSTREAM2(log_regularly, cerr))
    , f_debug( EZLOGGERVLSTREAM2(log_rarely, cerr))
    , f_drivel( EZLOGGERVLSTREAM2(log_very_rarely, cerr))
{
}

ezlogger<>& ConsoleMgr::err()
{
  if (OptsMgr::INSTANCE().color())
      f_err << red;
  return f_err;
}

ezlogger<>& ConsoleMgr::warn()
{
  if (OptsMgr::INSTANCE().color())
    f_warn << yellow;
  return f_warn;
}

ezlogger<>& ConsoleMgr::trace()
{
  if (OptsMgr::INSTANCE().color())
      f_err << green;
  return f_trace;
}

ezlogger<>& ConsoleMgr::info()
{
  if (OptsMgr::INSTANCE().color())
    f_info << cyan;
  return f_info;
}

ezlogger<>& ConsoleMgr::debug()
{
  if (OptsMgr::INSTANCE().color())
      f_debug << light_gray;
  return f_debug;
}

ezlogger<>& ConsoleMgr::drivel()
{
  if (OptsMgr::INSTANCE().color())
      f_drivel << light_gray;
  return f_drivel;
}

