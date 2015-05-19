/**
Copyright (C) 2015  Cristian Alfonso Prieto Sánchez

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have getTransmitErrorCountd a copy of the GNU General Public License
along with this program. If not, see <http://www.gnu.org/licenses/>.
*/

package ugr.cristian.serverVideoApp;

/**
*@author Cristian Alfonso Prieto Sánchez
*/

import java.lang.System;

import java.net.InetAddress;
import java.net.UnknownHostException;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Iterator;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.Map;
import java.util.HashMap;
import java.util.Set;
import java.util.HashSet;

import org.opendaylight.controller.sal.action.Action;
import org.opendaylight.controller.sal.action.Controller;
import org.opendaylight.controller.sal.action.Output;
import org.opendaylight.controller.sal.action.SetDlDst;
import org.opendaylight.controller.sal.action.SetDlSrc;
import org.opendaylight.controller.sal.action.SetNwDst;
import org.opendaylight.controller.sal.action.SetNwSrc;
import org.opendaylight.controller.sal.core.ConstructionException;
import org.opendaylight.controller.sal.core.Bandwidth;
import org.opendaylight.controller.sal.core.Node;
import org.opendaylight.controller.sal.core.Edge;
import org.opendaylight.controller.sal.core.Host;
import org.opendaylight.controller.sal.core.Latency;
import org.opendaylight.controller.sal.core.Property;
import org.opendaylight.controller.sal.core.Path;
import org.opendaylight.controller.sal.core.NodeConnector;
import org.opendaylight.controller.sal.flowprogrammer.Flow;
import org.opendaylight.controller.sal.flowprogrammer.IFlowProgrammerService;
import org.opendaylight.controller.sal.match.Match;
import org.opendaylight.controller.sal.match.MatchType;
import org.opendaylight.controller.sal.match.MatchField;
import org.opendaylight.controller.sal.packet.BitBufferHelper;
import org.opendaylight.controller.sal.packet.Ethernet;
import org.opendaylight.controller.sal.packet.IDataPacketService;
import org.opendaylight.controller.sal.packet.IListenDataPacket;
import org.opendaylight.controller.sal.packet.IPv4;
import org.opendaylight.controller.sal.packet.ICMP;
import org.opendaylight.controller.sal.packet.TCP;
import org.opendaylight.controller.sal.packet.UDP;
import org.opendaylight.controller.sal.packet.Packet;
import org.opendaylight.controller.sal.packet.PacketResult;
import org.opendaylight.controller.sal.packet.RawPacket;
import org.opendaylight.controller.sal.reader.FlowOnNode;
import org.opendaylight.controller.sal.reader.NodeConnectorStatistics;
import org.opendaylight.controller.sal.utils.IPProtocols;
import org.opendaylight.controller.sal.utils.Status;
import org.opendaylight.controller.switchmanager.ISwitchManager;
import org.opendaylight.controller.topologymanager.ITopologyManager;
import org.opendaylight.controller.statisticsmanager.IStatisticsManager;

import edu.uci.ics.jung.algorithms.shortestpath.DijkstraShortestPath;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.SparseMultigraph;
import edu.uci.ics.jung.graph.util.EdgeType;

import org.apache.commons.collections15.Transformer;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class RTPRouting {

	private static final Logger log = LoggerFactory.getLogger(PacketHandler.class);

		private Map<Node, Set<Edge>> nodeEdges = new HashMap<Node, Set<Edge>>();

		private Edge edgeMatrix[][];

		private Long latencyMatrix[][];
		private Long minLatency;
		private Long mediumLatencyMatrix[][];
		private Long minMediumLatency;

		private Long rtpCostMatrix[][];

		private ConcurrentMap<Edge, Map<String, ArrayList>> edgeStatistics = new ConcurrentHashMap<Edge, Map<String, ArrayList>>();
	  private Map<String, Long> maxStatistics = new HashMap<String, Long>();

		private Map<Edge, Long> edgeBandWith = new HashMap<Edge, Long>();
		private Long minBandWith;

		private Map<Edge, Long> rtpEdgeCostMap = new HashMap<Edge, Long>();

		private Transformer<Edge, ? extends Number> costRTPTransformer = null;

		private Graph<Node, Edge> g = new SparseMultigraph();
		private DijkstraShortestPath<Node, Edge> rtpShortestPath;

		private ConcurrentMap<Map<Node, Node>, List<Edge>> rtpPathMap = new ConcurrentHashMap<Map<Node, Node>, List<Edge>>();

		/*********Statistics Constants**********/

		private final String transmitBytes = "Transmits Bytes";
		private final String receiveBytes = "Receive Bytes";
		private final String transmitDropBytes = "Transmit Drop Bytes";
		private final String receiveDropBytes = "Receive Drop Bytes";
		private final String transmitErrorBytes = "Transmit Error Bytes";
		private final String receiveErrorBytes = "Receive Error Bytes";
		private final String[] statisticsName = {transmitBytes, receiveBytes, transmitDropBytes,
		receiveDropBytes, transmitErrorBytes, receiveErrorBytes};

		/***************************************/

		private final Integer rtpPort = 5004;
		private final Integer VERSION = 2;
		private final Integer M2PAYLOADTYPE = 33; //MPEG2
	  private final Long RTPFACTOR = 1000L; //To get the difference in ms
	  private final Long RTPDEFAULTCOST = 30L;
		private final Long DEFAULTBWCOST = 10L;
		/****************************************/
		public boolean needUpdate = false;

		/**
		*Constructor for RTPHandler class
		*@param nodes The nodeEdges map
		*@param edges The edgeMatrix
		*@param latencies The latencyMatrix
		*@param latency The min latency
		*@param medLatencies The mediumLatencyMatrix
		*@param medLatency The min mediumLatency value
		*@param statistics The edgeStatisticsMap
		*@param max The maximum statistics
		*@param grapho The topology Graph
		*@param bw The edge BandWith Map
		*@param minBW The minBW
		*/

		public RTPRouting(Map<Node, Set<Edge>> nodes, Edge edges[][], Long latencies[][], Long latency, Long medLatencies[][], Long medLatency,
		ConcurrentMap<Edge, Map<String, ArrayList>> statistics, Map<String, Long> max, Graph<Node, Edge> grapho, Map<Edge, Long> bw, Long minBW){

			this.nodeEdges = nodes;
			this.edgeMatrix = edges;
			this.latencyMatrix = latencies;
			this.minLatency = latency;
			this.mediumLatencyMatrix = medLatencies;
			this.minMediumLatency = medLatency;
			this.edgeStatistics = statistics;
			this.maxStatistics = max;
			this.edgeBandWith = bw;
			this.minBandWith = minBW;

			this.g = grapho;

			buildRTPCostMatrix();

		}

		static private InetAddress intToInetAddress(int i) {
	    byte b[] = new byte[] { (byte) ((i>>24)&0xff), (byte) ((i>>16)&0xff), (byte) ((i>>8)&0xff), (byte) (i&0xff) };
	    InetAddress addr;
	    try {
	        addr = InetAddress.getByAddress(b);
	    } catch (UnknownHostException e) {
	        return null;
	    }

	    return addr;
	  }

		/**
	  *This function try to assing a cost for each Edge attending The video factors
	  *which is different to Standard evaluation
	  */

	  private void buildRTPCostMatrix(){
	    int l = this.nodeEdges.size();
	    int h = this.nodeEdges.size();
	    this.rtpCostMatrix = new Long[l][h];
	    this.rtpEdgeCostMap.clear();

	    for(int i=0; i<l; i++){

	      for(int j=0; j<h; j++){

	        if(i==j){
	          this.rtpCostMatrix[i][j]=0L;
	        }
	        else if(this.edgeMatrix[i][j]==null){
	          this.rtpCostMatrix[i][j]=null;
	        }
	        else{

	          this.rtpCostMatrix[i][j] = rtpLatencyCost(this.edgeMatrix[i][j])/RTPFACTOR +
	          rtpStatisticsCost(this.edgeMatrix[i][j])/10 + rtpBandWithCost(this.edgeMatrix[i][j]);
	        }

	        this.rtpEdgeCostMap.put(this.edgeMatrix[i][j], this.rtpCostMatrix[i][j]);
	      }
	    }

	    buildRTPTransformerMap(this.rtpEdgeCostMap);

	  }

		/**
	  *Function that is called when is necessary to build the transformer rtp for Dijkstra
	  */

	  private void buildRTPTransformerMap(final Map<Edge, Long> rtpEdgeCostMap2){

	    this.costRTPTransformer = new Transformer<Edge, Long>(){
	      public Long transform(Edge e){

	        return rtpEdgeCostMap2.get(e);
	      }
	    };

	  }

		/**
    *This method provide the possibility to get a index for a nodeConnector
    *@param nodeConnector The nodeConnector.
    */

    private int getNodeConnectorIndex(NodeConnector nodeConnector){

      int index;
      Node node = nodeConnector.getNode();
      index = Integer.parseInt(node.getID().toString());
      return index-1;

    }

    /**
    *This function reordenate a Edge<List> to put in the correct order.
    *@param path The List<Edge>
    *@param srcNode The first Node
    *@param dstNode The last Node
    *@return The definitive List<Edge>
    */

    private List<Edge> reordenateList(List<Edge> path, Node srcNode, Node dstNode){
      boolean orden = true;
      boolean orientacion = true;

      List<Edge> result = new ArrayList();
      List<Edge> definitivePath = new ArrayList();

      if(path.get(0).getTailNodeConnector().getNode().equals(srcNode)){
        orden=true;
        orientacion=true;
      }
      else if(path.get(0).getHeadNodeConnector().getNode().equals(srcNode)){
        orden=true;
        orientacion=false;
      }
      else if(path.get(path.size()-1).getTailNodeConnector().getNode().equals(srcNode)){
        orden=false;
        orientacion=true;
      }
      else if(path.get(path.size()-1).getHeadNodeConnector().getNode().equals(srcNode)){
        orden=false;
        orientacion=false;
      }

      int i=0;
      int n1=0;
      int n2=0;

      if(!orden){
        i=path.size()-1;
      }
      int index;
      for(int j=0; j<path.size();j++){

        if(!orden){
          index=i-j;
        }
        else{
          index=j;
        }

        Edge tempEdge = path.get(index);

        if(!orientacion){
          n1=getNodeConnectorIndex(tempEdge.getHeadNodeConnector());
          n2=getNodeConnectorIndex(tempEdge.getTailNodeConnector());
        }else{
          n1=getNodeConnectorIndex(tempEdge.getTailNodeConnector());
          n2=getNodeConnectorIndex(tempEdge.getHeadNodeConnector());
        }
        result.add(this.edgeMatrix[n1][n2]);
      }

      ////////////////////////
      //Better reordenating
      ///////////////////////

      definitivePath.add(result.get(0));


      for(int j=1; j<result.size(); j++){

        Edge tempEdge2 = result.get(j);
        Edge tempEdge1 = result.get(j-1);

        Node tempNode1 = tempEdge1.getHeadNodeConnector().getNode();
        Node tempNode2 = tempEdge2.getTailNodeConnector().getNode();

        Node tempNodeAux = tempEdge2.getHeadNodeConnector().getNode();


        if(tempNode1.equals(tempNode2)){
          definitivePath.add(result.get(j));
        }else if(tempNode1.equals(tempNodeAux)){
          int aux1 = getNodeConnectorIndex(tempEdge2.getHeadNodeConnector());
          int aux2 = getNodeConnectorIndex(tempEdge2.getTailNodeConnector());

          definitivePath.add(this.edgeMatrix[aux1][aux2]);
        }
      }

      return definitivePath;

    }

		/**
    *This function is called when is necessary evaluate the latencyMatrix for an edge and
    *rtp protocol
    *@param edge The edge
    *@return The Long value after the process
    */

    private Long rtpLatencyCost(Edge edge){
      int i = getNodeConnectorIndex(edge.getTailNodeConnector());
      int j = getNodeConnectorIndex(edge.getHeadNodeConnector());

      Long ret1 = 0L;
      Long ret2 = 0L;

      Long cost = 0L;
      if(latencyMatrix!=null){
        Long temp1 = this.latencyMatrix[i][j];
        Long temp2 = this.mediumLatencyMatrix[i][j];

        if(temp1 == null){
          ret1=RTPDEFAULTCOST;
        }
        if(temp2 == null){
          ret2=RTPDEFAULTCOST;
        }

        if(temp1 != null && temp2 != null){
          if(temp1>temp2){
            cost = (temp1 - temp2)/2;
          }
          else if (temp2>temp1){
            cost = (temp2 - temp1)/2;
          }else{
            cost = RTPDEFAULTCOST*2;
          }
        }
      }
      else{
        ret1=RTPDEFAULTCOST;
        ret2=RTPDEFAULTCOST;
        cost=ret1+ret2;
      }
      return cost;
    }

		/**
    *This function is called when is necessary evaluate the statisticsMap for an edge and
    *rtp protocol
    *@param edge The edge
    *@return The Long value after the process
    */

    private Long rtpStatisticsCost(Edge edge){
      Long cost = 0L;
      Long temp1 = 0L;
      Long temp2 = 0L;

      ArrayList<Long> tempArray = new ArrayList<Long>();

      Map<String, ArrayList> tempStatistics = this.edgeStatistics.get(edge);
      for(int i=0; i<statisticsName.length; i++){
        tempArray = tempStatistics.get(statisticsName[i]);

        if(tempArray == null){

          tempArray=new ArrayList<Long>();
          tempArray.add(10L);
          tempArray.add(10L);

        }

        if(tempArray.get(0)!=0 && tempArray.get(1) !=0 ){
          Long tempMedium = (tempArray.get(0) + tempArray.get(1) )/ 2;

          Long tempMax = maxStatistics.get(statisticsName[i]);

          if(tempMax == null){
            tempMax = tempMedium;
          }


          if(tempMax/tempMedium > 9){
            cost += 1L;
          }
          else{
            cost += 10L - tempMax/tempMedium;
          }
        }
        else{
          cost += 1L;
        }
      }
      return cost/5;
    }

		/**
		*This function return the cost for the BandWith of a Edge
		*@param edge The edge
		*@return result The Long value after evaluation
		*/

		private Long rtpBandWithCost(Edge edge){
			Long edgeBW = this.edgeBandWith.get(edge);
			Long result = DEFAULTBWCOST;

			if(edgeBW != null && edgeBW != 0L){
				result = edgeBW / minBandWith;
			}
			return result;
		}

		/**
		*Function that is called when we pretend to show in log all the elements of a Matrix
		*@matrix[][] The matrix
		*/

		private void traceLongMatrix(Long matrix[][]){

			for(int i=0; i<matrix.length; i++){
				for(int j=0; j<matrix[i].length; j++){

					log.debug("Element "+i+ " "+j+" is: "+matrix[i][j]);

				}
			}

		}
		/******************************PUBLIC METHODS*****************************

		//-128, -95 are the number value of the two first packets rtp which combined with the destination port are enough to detect rtp packet and program flow

		//H263 es dinámico y está entre los asignar (del 77 al 95) asumimos 95

		//https://www.ietf.org/rfc/rfc3551.txt

    /*
    Número de versión de RTP (V - versión number): 2 bits. La versión definida por la especificación actual es 2.
    Relleno (P - Padding): 1 bit. Si el bit del relleno está activado, hay uno o más bytes al final del paquete que no es parte de la carga útil. El último byte del paquete indica el número de bytes de relleno. El relleno es usado por algunos algoritmos de cifrado.
    La extensión (X - Extensión): 1 bit. Si el bit de extensión está activado, entonces el encabezado fijo es seguido por una extensión del encabezado. Este mecanismo de la extensión posibilita implementaciones para añadir información al encabezado RTP.
    Conteo CSRC (CC): 4 bits. El número de identificadores CSRC que sigue el encabezado fijo. Si la cuenta CSRC es cero, entonces la fuente de sincronización es la fuente de la carga útil.
    El marcador (M - Marker): 1 bit. Un bit de marcador definido por el perfil particular de media.
    Tipo de Carga útil (PT - Payload Type): 7 bits. Un índice en una tabla del perfiles de media que describe el formato de carga útil. Los mapeos de carga útil para audio y vídeo están especificados en el RFC 1890.
    */

    /**
    *Function that is called when is necessary to check if a Packet is RTP
    *@param rawPayload The payload of the packet
    *@param dstPort The dstPort for the packet
    *@return True or false.
    */

    public boolean detectRTPPacket(byte[] rawPayload, int dstPort){
      boolean result = false;

      if(dstPort == rtpPort){
        Byte temp = rawPayload[0];
				Integer tempVersion = (Integer)(temp & 0xC0)>>6;

				Byte temp2 = rawPayload[1];
				Integer tempType = (Integer)(temp2 & 0x7F);

        if(tempVersion == VERSION){
					if(tempType == M2PAYLOADTYPE){
						result=true;
					}
        }
      }

      return result;
    }

		/**
		*This fucntion is called when is necessary get the best path between two nodes
		*@param srcNode The srcNode
		*@param dstNode The dstNode
		*@return result The resultan path
		*/

		public List<Edge> getRTPShortestPath(Node srcNode, Node dstNode){

			if(this.g == null || this.g.getEdgeCount() == 0){
				needUpdate = true;
			}

			Map<Node, Node> tempMap = new HashMap<Node, Node>();
			tempMap.put(srcNode, dstNode);

			List<Edge> tempPath = new ArrayList<Edge>();
      List<Edge> definitivePath = new ArrayList<Edge>();

			if(rtpPathMap.containsKey(tempMap)){
				tempPath = rtpPathMap.get(tempMap);
			}else{
				this.rtpShortestPath = new DijkstraShortestPath<Node,Edge>(this.g, this.costRTPTransformer);
				tempPath = rtpShortestPath.getPath(srcNode, dstNode);
				rtpPathMap.put(tempMap, tempPath);
			}

      boolean temp = tempPath.get(0).getTailNodeConnector().getNode().equals(srcNode);

      if(!temp){
        definitivePath = reordenateList(tempPath, srcNode, dstNode);
      }
      else{
        definitivePath = tempPath;
      }
  		return definitivePath;

		}

		/**
		*This function del old RTP flows when an Edge is down
		*@param edge The Edge which is down now
		*@param flowProgrammer The service which enable the posibility to del or install flows
		*@param statisticsManager The statistics manager to obtain the flows on a Node.
		*/

		public boolean removeFlows(Edge edge, IFlowProgrammerService flowProgrammerService, IStatisticsManager statisticsManager){
			Set<Map<Node, Node>> tempMaps = rtpPathMap.keySet();
			boolean result = false;
			if(tempMaps.isEmpty()){
				result = true;
				Set<Node> nodes = this.nodeEdges.keySet();

				for(Iterator it = nodes.iterator(); it.hasNext();){
					Node tempNode = (Node)it.next();

					List<FlowOnNode> flowsOnNode = new ArrayList();

					try{
						flowsOnNode = statisticsManager.getFlows(tempNode);
					}
					catch(RuntimeException bad){
						log.trace("No flows get, time to try in noCache flows");
						try{
							flowsOnNode = statisticsManager.getFlowsNoCache(tempNode);
						}
						catch(RuntimeException veryBad){
							log.trace("Impossible to obtain the flows");
						}
					}

					for(int j = 0; j<flowsOnNode.size(); j++){
						FlowOnNode tempFlowOnNode = flowsOnNode.get(j);
						Flow tempFlow = tempFlowOnNode.getFlow();

						if(tempFlow!=null){
							MatchField tempField = tempFlow.getMatch().getField(MatchType.NW_PROTO);
							MatchField tempField3 = tempFlow.getMatch().getField(MatchType.TP_DST);
							MatchField tempField2 = new MatchField(MatchType.NW_PROTO, IPProtocols.UDP.byteValue());
							MatchField tempField4 = new MatchField(MatchType.TP_DST, rtpPort.shortValue());

							if(tempField.equals(tempField2)&& tempField3.equals(tempField4)){
								try{
									log.trace("Trying removing "+tempFlow+" on "+tempNode);
									flowProgrammerService.removeFlow(tempNode, tempFlow);
								}
								catch(RuntimeException e8){
									log.trace("Error removing flow");
								}
							}
						}
					}
				}
			}
			else{
				for(Iterator it = tempMaps.iterator(); it.hasNext();){
					Map<Node, Node> tempMap = (Map<Node, Node>)it.next();
					List<Edge> tempPath = rtpPathMap.get(tempMap);

					if(tempPath.contains(edge)){

						for(int i=0; i<tempPath.size(); i++){
							Edge tempEdge = tempPath.get(i);
							Node tempNode = tempEdge.getTailNodeConnector().getNode();

							List<FlowOnNode> flowsOnNode = new ArrayList();

							try{
								flowsOnNode = statisticsManager.getFlows(tempNode);
							}
							catch(RuntimeException bad){
								log.trace("No flows get, time to try in noCache flows");
								try{
									flowsOnNode = statisticsManager.getFlowsNoCache(tempNode);
								}
								catch(RuntimeException veryBad){
									log.trace("Impossible to obtain the flows");
								}
							}

							for(int j = 0; j<flowsOnNode.size(); j++){
								FlowOnNode tempFlowOnNode = flowsOnNode.get(j);
								Flow tempFlow = tempFlowOnNode.getFlow();

								if(tempFlow!=null){
									MatchField tempField = tempFlow.getMatch().getField(MatchType.NW_PROTO);
									MatchField tempField3 = tempFlow.getMatch().getField(MatchType.TP_DST);
									MatchField tempField2 = new MatchField(MatchType.NW_PROTO, IPProtocols.UDP.byteValue());
									MatchField tempField4 = new MatchField(MatchType.TP_DST, rtpPort.shortValue());

									if(tempField.equals(tempField2)&& tempField3.equals(tempField4)){
										try{
											log.trace("Trying removing "+tempFlow+" on "+tempNode);
											flowProgrammerService.removeFlow(tempNode, tempFlow);
										}
										catch(RuntimeException e8){
											log.trace("Error removing flow");
										}
									}
								}
							}
						}
						for(int i=0; i<tempPath.size(); i++){
							Edge tempEdge = tempPath.get(i);
							Node tempNode = tempEdge.getHeadNodeConnector().getNode();

							List<FlowOnNode> flowsOnNode = new ArrayList();

							try{
								flowsOnNode = statisticsManager.getFlows(tempNode);
							}
							catch(RuntimeException bad){
								log.trace("No flows get, time to try in noCache flows");
								try{
									flowsOnNode = statisticsManager.getFlowsNoCache(tempNode);
								}
								catch(RuntimeException veryBad){
									log.trace("Impossible to obtain the flows");
								}
							}

							for(int j = 0; j<flowsOnNode.size(); j++){
								FlowOnNode tempFlowOnNode = flowsOnNode.get(j);
								Flow tempFlow = tempFlowOnNode.getFlow();

								if(tempFlow!=null){
									MatchField tempField = tempFlow.getMatch().getField(MatchType.NW_PROTO);
									MatchField tempField3 = tempFlow.getMatch().getField(MatchType.TP_DST);
									MatchField tempField2 = new MatchField(MatchType.NW_PROTO, IPProtocols.UDP.byteValue());
									MatchField tempField4 = new MatchField(MatchType.TP_DST, rtpPort.shortValue());


									if(tempField.equals(tempField2) && tempField3.equals(tempField4)){
										try{
											log.trace("Trying removing "+tempFlow+" on "+tempNode);
											flowProgrammerService.removeFlow(tempNode, tempFlow);
										}
										catch(RuntimeException e8){
											log.trace("Error removing flow");
										}
									}
								}
							}
						}
					}
				}
			}
			return result;
		}


		/**
		*Function that is called when is necessary to update a TopologyGraph
		*@param grafo The new graph
		*/

		public void updateGraph(Graph grafo){
			this.g=grafo;
		}

		/**
		*Function that is called when is necessary to update the rtpCostMartix
		*@param latencies The latencyMatrix
		*@param latency The min latency
		*@param medLatencies The mediumLatencyMatrix
		*@param medLatency The min mediumLatency value
		*@param statistics The edgeStatisticsMap
		*@param max The maximum statistics
		*@param bw The edge BandWith Map
		*@param minBW The minBW
		*/

		public void updateRTPCostMatrix(Long latencies[][], Long latency, Long medLatencies[][], Long medLatency,
		ConcurrentMap<Edge, Map<String, ArrayList>> statistics, Map<String, Long> max, Map<Edge, Long> bw, Long minBW){

			this.latencyMatrix = latencies;
			this.minLatency = latency;
			this.mediumLatencyMatrix = medLatencies;
			this.minMediumLatency = medLatency;
			this.edgeStatistics = statistics;
			this.maxStatistics = max;
			this.edgeBandWith = bw;
			this.minBandWith = minBW;

			buildRTPCostMatrix();

		}
}
