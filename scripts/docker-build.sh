#!/usr/bin/env bash
cd docker/hub
DOCKER_BUILD_TAG=$1
echo "Docker build tag: " $DOCKER_BUILD_TAG
if [[ "$DOCKER_BUILD_TAG" = "latest" ]]; then
        echo "tag - master"
	docker build --build-arg BUILD_TAG="master" --no-cache=true --tag parity/parity:$DOCKER_BUILD_TAG .
else
         echo "not master"
	docker build --build-arg BUILD_TAG=$DOCKER_BUILD_TAG --no-cache=true --tag parity/parity:$DOCKER_BUILD_TAG .
fi
echo "docker run"
docker run -it poanetwork/parity:$DOCKER_BUILD_TAG -v
echo "docker push"
docker push poanetwork/parity:$DOCKER_BUILD_TAG
