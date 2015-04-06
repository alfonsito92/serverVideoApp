SERVERVIDEO

The serverVideoApp solve the actual routing problem. We supposse that in the net all the video packets have the same dstPort
and use RTP. The rest of packets will be discard.

This app try to use the Dijkstra algorithm but changing the weight Map (Actually
we can find the Dijkstra implementation to ODL here
https://github.com/lbchen/ODL/tree/master/opendaylight/routing/dijkstra_implementation/src).

I pretend to use the differents NodeConnector statistics combine with link properties to
build a weight Matrix and then apply the Dijkstra Algorithm to build the best path.

PROBLEMS
Problem 1.
The properties of the link are empty. This problem cause a lot of variations
in the source Code because now It's impossible to know the bandwith or the latency in the
edges. The temporaly solution is about build a latencyMap through the flood packet and use
this latency to build the weightMatrix.

THANKS
Thanks to SDNHubTutorials, SDNtutorials and Frank dürr

http://sdnhub.org/tutorials/opendaylight/

http://sdnhub.org/tutorials/opendaylight/

http://www.frank-durr.de/
