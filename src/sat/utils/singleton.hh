// -*- C++ -*-

// Singleton.h: Template for 'Singleton' objects.
// Author: Alessandro Santuari

#ifndef SINGLETON_H_INCLUDED
#define SINGLETON_H_INCLUDED

#include <assert.h>
#include <cstring>

namespace Minisat {

template <typename T> class Singleton {
public:
    Singleton()
    {
        assert( !the_singleton );
        size_t offset = (size_t)(T*)1 - (size_t)(Singleton <T>*)(T*)1;
        the_singleton = (T*)((size_t)this + offset);
    }

    ~Singleton()
    {
        assert( the_singleton );
        the_singleton = 0;
    }

    static inline T& get()
    {
        assert( the_singleton );
        return ( *the_singleton );
    }

    static inline T* get_ptr()
    {
        return ( the_singleton );
    }

    // Checks whether the singleton has already been built
    static inline bool is_alive()
    {
        return (the_singleton != 0 );
    }

protected:
    static T* the_singleton;
};

template <typename T> T* Singleton <T>::the_singleton = 0;

}

#endif // SINGLETON_H_INCLUDED
