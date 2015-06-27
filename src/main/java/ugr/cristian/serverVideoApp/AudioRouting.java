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
import org.opendaylight.controller.sal.match.MatchField;
import org.opendaylight.controller.sal.match.MatchType;
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

public class AudioRouting {

	private static final Logger log = LoggerFactory.getLogger(PacketHandler.class);

		private Map<Node, Set<Edge>> nodeEdges = new HashMap<Node, Set<Edge>>();

		private Edge edgeMatrix[][];

		private Long latencyMatrix[][];
		private Long minLatency;
		private Long mediumLatencyMatrix[][];
		private Long minMediumLatency;
		private Long maxMediumLatency;

		private Long jitterMatrix[][];
		private Long minJitter;
		private Long maxJitter;

		private Double audioCostMatrix[][];

		private ConcurrentMap<Edge, Map<String, ArrayList>> edgeStatistics = new ConcurrentHashMap<Edge, Map<String, ArrayList>>();
	  private Map<String, Long> maxStatistics = new HashMap<String, Long>();

		private Map<Edge, Double> audioEdgeCostMap = new HashMap<Edge, Double>();

    private Map<Edge, Long> edgeBandWith = new HashMap<Edge, Long>();
		private Long minBandWith;

		private Transformer<Edge, ? extends Number> costAudioTransformer = null;

		private Graph<Node, Edge> g = new SparseMultigraph();
		private DijkstraShortestPath<Node, Edge> audioShortestPath;

		private ConcurrentMap<Map<Node, Node>, List<Edge>> audioPathMap = new ConcurrentHashMap<Map<Node, Node>, List<Edge>>();

		/******************************/
		private Double aL=0.0;
		private Double bL=0.0;

		private Double aJ=0.0;
		private Double bJ=0.0;

		private Double latMin=5.0;
		private Double jitMin=2.0;

		private Double nsTOms = 1000000.0;

		private Double alpha=1.0;
		private Double beta=1.0;
		private Double gamma=10.0;
		private Double sigma = 0.0;
		/******************************/

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

		private final Integer audioPort = 30000;
		private final Integer VERSION = 2;
		private final Integer TYPE = 0; //G711.ITU PCMU
	  private final Long AUDIOFACTOR = 1000L; //To get the difference in ms
	  private final Long AUDIODEFAULTCOST = 500L;
    private final Long DEFAULTBWCOST = 10L;
		/****************************************/
		public boolean needUpdate = false;

		/**
		*Constructor for AUDIOHandler class
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

		public AudioRouting(Map<Node, Set<Edge>> nodes, Edge edges[][], Long latencies[][], Long latency, Long medLatencies[][], Long medLatency,
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

			buildAudioParameters();

			buildAudioCostMatrix();
			this.audioPathMap = new ConcurrentHashMap<Map<Node, Node>, List<Edge>>();
			buildAudioTransformerMap(this.audioEdgeCostMap);

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
		*This function return the cost for the BandWith of a Edge
		*@param edge The edge
		*@return result The Long value after evaluation
		*/

		private Long audioBandWithCost(Edge edge){
			Long edgeBW = this.edgeBandWith.get(edge);
			Long result = DEFAULTBWCOST;

			if(edgeBW != null && edgeBW != 0L){
				result = edgeBW / minBandWith;
			}
			return result;
		}

		/**
	  *Function that is called when is necessary evaluate the cost associated to jitter
	  *in a edge
	  *@param edge The edge
	  *@return cost The associated cost
	  */

	  private Double audioEvaluationJitterCost(Edge edge){
	    int i = getNodeConnectorIndex(edge.getTailNodeConnector());
	    int j = getNodeConnectorIndex(edge.getHeadNodeConnector());

	    Double cost=10.0;

	    if((maxJitter-minJitter)/nsTOms > jitMin){
	      if(aJ!=null && bJ!=null && jitterMatrix[i][j]!=null){
	        cost = jitterMatrix[i][j]*aJ/nsTOms + bJ;
	      }
	    }
	    else{
	      cost = 10.0;
	    }
	    if(aL!=null && aL<1.0){
	      cost = aL*cost;
	    }

	    return cost;
	  }

	  /**
	  *This function is called when is necessary evaluate the latencyMatrix for an edge
	  *@param edge The edge
	  *@return The double value after the process
	  */

	  private Double audioEvaluationLatencyCost(Edge edge){
	    int i = getNodeConnectorIndex(edge.getTailNodeConnector());
	    int j = getNodeConnectorIndex(edge.getHeadNodeConnector());

	    Double cost=0.0;
	    if((maxMediumLatency-minMediumLatency)/nsTOms > latMin){
	      if(aL!=null && bL!=null && mediumLatencyMatrix[i][j]!=null){
	        cost = mediumLatencyMatrix[i][j]*aL/nsTOms + bL;
	      }
	    }
	    else{
	      cost = 10.0;
	    }

	    return cost;
	  }

	  /**
	  *This function is called when ins necessary evaluate the loss cost for a edge.
	  *@param edge The edge
	  *@return cost The double value (percent)
	  */

	  private Double audioEvaluationLossCost(Edge edge){

	    Double cost = 0.0;
	    ArrayList<Long> temp1 = new ArrayList<Long>();
	    ArrayList<Long> temp2 = new ArrayList<Long>();

	    Map<String, ArrayList> tempStatistics = this.edgeStatistics.get(edge);

	    temp1 = tempStatistics.get(transmitBytes);
	    temp2 = tempStatistics.get(receiveBytes);


	    if( temp1 == null || temp2 == null ){
	      return cost;
	    }else{
	      Long sent = temp1.get(1); //The 1 correspond to tailConnector and 0 to headConnector
	      Long receive = temp2.get(0);



	      if(sent!=null && receive!=null){
	        if(sent>receive){
	          cost = ((double)sent - (double)receive)*100.0;
	          cost = cost/(double)sent;
	        }
	        else{
	          return 0.0;
	        }
	      }

	    }
	    return cost;
	  }

		/**
	  *This function try to assing a cost for each Edge attending The video factors
	  *which is different to Standard evaluation
	  */

	  private void buildAudioCostMatrix(){
	    int l = this.nodeEdges.size();
	    int h = this.nodeEdges.size();
	    this.audioCostMatrix = new Double[l][h];
	    this.audioEdgeCostMap.clear();

	    for(int i=0; i<l; i++){

	      for(int j=0; j<h; j++){

	        if(i==j){
	          this.audioCostMatrix[i][j]=0.0;
	        }
	        else if(this.edgeMatrix[i][j]==null){
	          this.audioCostMatrix[i][j]=null;
	        }
	        else{

	          this.audioCostMatrix[i][j] = alpha*audioEvaluationLatencyCost(this.edgeMatrix[i][j])+
						beta*audioEvaluationJitterCost(this.edgeMatrix[i][j])+gamma*audioEvaluationLossCost(this.edgeMatrix[i][j]);
	        }

	        this.audioEdgeCostMap.put(this.edgeMatrix[i][j], this.audioCostMatrix[i][j]);
	      }
	    }

	    buildAudioTransformerMap(this.audioEdgeCostMap);

	  }

		/**
	  *This function build the jitter matrix and the aL, bL, aJ, bJ parameters
	  */

	  private void buildAudioParameters(){

	    if(this.mediumLatencyMatrix != null){

				this.maxMediumLatency = findMaxMatrix(this.mediumLatencyMatrix);
				this.minMediumLatency = findMinMatrix(this.mediumLatencyMatrix);

	      if(this.maxMediumLatency!=null && this.minMediumLatency!=null){
	        Double min = this.minMediumLatency/nsTOms;
	        Double max = this.maxMediumLatency/nsTOms;
	        bL = (max - 100.0*min)/(max - min);
					aL = (1-bL)/min;
				}

			}

	    createAudioJitterMatrix();

	    if(this.jitterMatrix != null && this.jitterMatrix.length>0){

					this.minJitter = findMinMatrix(this.jitterMatrix);
					this.maxJitter = findMaxMatrix(this.jitterMatrix);

					if(this.minJitter!=null && this.maxJitter!=null){
	          Double min = this.minJitter/nsTOms;
	          Double max = this.maxJitter/nsTOms;
	          bJ = (max - 100.0*min)/(max - min);
	          if(bJ!=1){
	            aJ = (1-bJ)/min;
	          }else{
	            aJ = 1.0;
	          }

					}

				}

	  }

		/**
	  *Function that is called when is necessary to build the transformer audio for Dijkstra
	  */

	  private void buildAudioTransformerMap(final Map<Edge, Double> audioEdgeCostMap2){

	    this.costAudioTransformer = new Transformer<Edge, Number>(){
	      public Double transform(Edge e){

	        return audioEdgeCostMap2.get(e);
	      }
	    };

	  }

		/**
		*Function that is called when is neccesary to create the jitter Matrix
		*/

		private void createAudioJitterMatrix(){

			this.jitterMatrix = new Long[this.nodeEdges.size()][this.nodeEdges.size()];

			for(int i=0; i<jitterMatrix.length; i++){

				for(int j=0; j<jitterMatrix.length; j++){

					if(this.latencyMatrix[i][j]!=null && this.mediumLatencyMatrix!=null){
						jitterMatrix[i][j]=Math.abs(this.latencyMatrix[i][j]-this.mediumLatencyMatrix[i][j]);
					}

				}
			}

		}

		/**
		*This function returns the max value in a matrix
		*@param matrix The matrix
		*@return The max vale
		*/

		private Long findMaxMatrix(Long matrix[][]){
			Long resultado = 0L;
			for(int i=0; i<matrix.length; i++){
				for(int j=0; j<matrix.length; j++){
					if(matrix[i][j]!=null){
						if(resultado<matrix[i][j]){
							resultado=matrix[i][j];
						}
					}
				}
			}
			return resultado;
		}

		/**
		*This function return the min Value in a Matrix
		*@param matrix The matrix
		*@return the min value
		*/

		private Long findMinMatrix(Long matrix[][]){
			Long resultado = 100000000000L;
			for(int i=0; i<matrix.length; i++){
				for(int j=0; j<matrix.length; j++){
					if(matrix[i][j]!=null){
						if(resultado>matrix[i][j]){
							resultado=matrix[i][j];
						}
					}
				}
			}
			return resultado;
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
			List<Edge> result = new ArrayList();
			List<Edge> definitivePath = new ArrayList();
			//log.debug("path(0) "+path.get(0)+" head "+path.get(0).getHeadNodeConnector().getNode()+
			//" tail " +path.get(0).getTailNodeConnector().getNode());
			result = path;

			for (int i = 0; i<path.size(); i++){
				if(result.get(i).getTailNodeConnector().getNode().equals(srcNode)){
					definitivePath.add(path.get(i));
					result.remove(i);
					break;
				}
				else if(result.get(i).getHeadNodeConnector().getNode().equals(srcNode)){
					Edge temp = result.get(i);
					int aux1 = getNodeConnectorIndex(temp.getHeadNodeConnector());
					int aux2 = getNodeConnectorIndex(temp.getTailNodeConnector());
					definitivePath.add(this.edgeMatrix[aux1][aux2]);
					result.remove(i);
					break;
				}
			}

			while(result.size()!=0){

				int i=0;

				Edge tempEdge = result.get(i);
				int tempSize = definitivePath.size();
				if(tempSize>0){
					Edge tempEdge2 = definitivePath.get(tempSize-1);
					Node nodeHeadPrevious = tempEdge2.getHeadNodeConnector().getNode();

					Node tempNode1 = tempEdge.getHeadNodeConnector().getNode();
					Node tempNode2 = tempEdge.getTailNodeConnector().getNode();

					if(nodeHeadPrevious.equals(tempNode2)){
						definitivePath.add(tempEdge);
						result.remove(i);
						i=0;
					}else if(nodeHeadPrevious.equals(tempNode1)){
						int aux1 = getNodeConnectorIndex(tempEdge.getHeadNodeConnector());
						int aux2 = getNodeConnectorIndex(tempEdge.getTailNodeConnector());

						definitivePath.add(this.edgeMatrix[aux1][aux2]);
						result.remove(i);
						i=0;
					}
				}else{
					return null;
				}
				i++;
			}
			return definitivePath;
    }

		/**
    *This function is called when is necessary evaluate the latencyMatrix for an edge and
    *audio protocol
    *@param edge The edge
    *@return The Long value after the process
    */

    private Long audioLatencyCost(Edge edge){
      int i = getNodeConnectorIndex(edge.getTailNodeConnector());
      int j = getNodeConnectorIndex(edge.getHeadNodeConnector());

      Long ret1 = 0L;
      Long ret2 = 0L;

      Long cost = 0L;
      if(latencyMatrix!=null){
        Long temp1 = this.latencyMatrix[i][j];
        Long temp2 = this.mediumLatencyMatrix[i][j];

        if(temp1 == null){
          ret1=AUDIODEFAULTCOST;
        }
        if(temp2 == null){
          ret2=AUDIODEFAULTCOST;
        }

        if(temp1 != null && temp2 != null){
          if(temp1>temp2){
						cost = temp1-temp2;
					}else{
						cost = temp2 -temp1;
					}
					cost += temp2;
        }
      }
      else{
        ret1=AUDIODEFAULTCOST;
        ret2=AUDIODEFAULTCOST;
        cost=ret1+ret2;
      }
      return cost;
    }

		/**
    *This function is called when is necessary evaluate the statisticsMap for an edge and
    *audio protocol
    *@param edge The edge
    *@return The Long value after the process
    */

    private Long audioStatisticsCost(Edge edge){
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
		*Function that is called when we pretend to show in log all the elements of a Double Matrix
		*@param matrix[][] The matrix
		*/

		private void traceDoubleMatrix(Double matrix[][]){

			for(int i=0; i<matrix.length; i++){
				for(int j=0; j<matrix[i].length; j++){

					log.debug("Element "+i+ " "+j+" is: "+matrix[i][j]);

				}
			}

		}

		/******************************PUBLIC METHODS*****************************

    /**
    *Function that is called when is necessary to check if a Packet is Audio
    *@param rawPayload The payload of the packet
    *@param dstPort The dstPort for the packet
    *@return True or false.
    */

    public boolean detectAudioPacket(byte[] rawPayload, int dstPort){
			boolean result = false;

			if(dstPort == audioPort){
				Byte temp = rawPayload[0];
				Integer tempVersion = (Integer)(temp & 0xC0)>>6;

				Byte temp2 = rawPayload[1];
				Integer tempType = (Integer)(temp2 & 0x7F);
				log.debug("tempVersion y type "+tempVersion+" "+tempType);
				if(tempVersion == VERSION){
					if(tempType == TYPE){
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

		public List<Edge> getAudioShortestPath(Node srcNode, Node dstNode){

			if(this.g == null || this.g.getEdgeCount() == 0){
				needUpdate = true;
			}

			Map<Node, Node> tempMap = new HashMap<Node, Node>();
			tempMap.put(srcNode, dstNode);

			List<Edge> tempPath = new ArrayList<Edge>();
      List<Edge> definitivePath = new ArrayList<Edge>();

			this.audioShortestPath = new DijkstraShortestPath<Node,Edge>(this.g, this.costAudioTransformer);
			tempPath = audioShortestPath.getPath(srcNode, dstNode);



			//boolean temp = tempPath.get(0).getTailNodeConnector().getNode().equals(srcNode);
	    //log.debug("tempPath "+tempPath);
	    //if(!temp){
	      definitivePath = reordenateList(tempPath, srcNode, dstNode);
				if(audioPathMap.containsKey(definitivePath)){
					tempPath = audioPathMap.remove(definitivePath);
				}
				audioPathMap.put(tempMap, definitivePath);
	    //}
	    //else{
	      //definitivePath = tempPath;
	    //}
	    //log.debug("srcNode "+srcNode+" dstNode "+dstNode);
	    //log.debug("path "+definitivePath);

  		return definitivePath;

		}

		/**
		*This function del old Audio flows when an Edge is down
		*@param edge The Edge which is down now
		*@param flowProgrammer The service which enable the posibility to del or install flows
		*@param statisticsManager The statistics manager to obtain the flows on a Node.
		*/

		public boolean removeFlows(Edge edge, IFlowProgrammerService flowProgrammerService, IStatisticsManager statisticsManager){
			Set<Map<Node, Node>> tempMaps = audioPathMap.keySet();
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
							MatchField tempField4 = new MatchField(MatchType.TP_DST, audioPort.shortValue());

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
					List<Edge> tempPath = audioPathMap.get(tempMap);

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
									MatchField tempField4 = new MatchField(MatchType.TP_DST, audioPort.shortValue());

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
									MatchField tempField4 = new MatchField(MatchType.TP_DST, audioPort.shortValue());


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
		*Function that is called when is necessary to update the audioCostMartix
		*@param latencies The latencyMatrix
		*@param latency The min latency
		*@param medLatencies The mediumLatencyMatrix
		*@param medLatency The min mediumLatency value
		*@param statistics The edgeStatisticsMap
		*@param max The maximum statistics
    *@param bw The edge BandWith Map
    *@param minBW The minBW
		*/

		public void updateAudioCostMatrix(Map<Node, Set<Edge>> nodes, Edge edges[][], Long latencies[][], Long latency, Long medLatencies[][], Long medLatency,
		ConcurrentMap<Edge, Map<String, ArrayList>> statistics, Map<String, Long> max, Map<Edge, Long> bw, Long minBW){

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

			buildAudioParameters();
			buildAudioCostMatrix();
			//log.debug("Matriz de costes de audio");
			//traceDoubleMatrix(this.audioCostMatrix);
		}

  }
