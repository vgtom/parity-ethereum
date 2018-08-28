#!/usr/bin/env bash

set -e # fail on any error
set -u # treat unset variables as error

echo "Pushing release, url: " "http://45.32.70.198:1339/push-release/"$CI_BUILD_REF_NAME"/"$CI_BUILD_REF

DATA="secret=$RELEASES_SECRET"

echo "Pushing release to Mainnet"
./scripts/safe_curl.sh $DATA "http://45.32.70.198:1337/push-release/$CI_BUILD_REF_NAME/$CI_BUILD_REF"

echo "Pushing release to Kovan"
./scripts/safe_curl.sh $DATA "http://45.32.70.198:1338/push-release/$CI_BUILD_REF_NAME/$CI_BUILD_REF"

echo "Pushing release to Sokol"
./scripts/safe_curl.sh $DATA "http://45.32.70.198:1339/push-release/$CI_BUILD_REF_NAME/$CI_BUILD_REF"
