#!/bin/bash

debuild -eDEB_BUILD_OPTIONS="parallel=8" -us -uc -b
