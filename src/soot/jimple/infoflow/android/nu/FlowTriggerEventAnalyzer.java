package soot.jimple.infoflow.android.nu;

import java.io.IOException;
import java.text.MessageFormat;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.logging.Formatter;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.LogRecord;
import java.util.logging.Logger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import nu.analysis.DefAnalysisMap;
import nu.analysis.IntraProcedureAnalysis;
import nu.analysis.values.CallRetValue;
import nu.analysis.values.ConstantValue;
import nu.analysis.values.InstanceFieldValue;
import nu.analysis.values.RightValue;

import com.sun.xml.internal.bind.v2.model.core.ID;

import soot.Immediate;
import soot.Local;
import soot.MethodOrMethodContext;
import soot.PointsToAnalysis;
import soot.PointsToSet;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AnyNewExpr;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.BinopExpr;
import soot.jimple.CastExpr;
import soot.jimple.ConcreteRef;
import soot.jimple.Constant;
import soot.jimple.DefinitionStmt;
import soot.jimple.Expr;
import soot.jimple.FieldRef;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InstanceOfExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewExpr;
import soot.jimple.NewMultiArrayExpr;
import soot.jimple.NullConstant;
import soot.jimple.NumericConstant;
import soot.jimple.ParameterRef;
import soot.jimple.Ref;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.ThisRef;
import soot.jimple.UnopExpr;
import soot.jimple.infoflow.Infoflow;
import soot.jimple.infoflow.android.manifest.ProcessManifest;
import soot.jimple.infoflow.android.nu.FlowTriggerEventObject.EventID;
import soot.jimple.infoflow.android.nu.FlowTriggerEventObject.EventOriginObject;
import soot.jimple.infoflow.android.resources.ARSCFileParser;
import soot.jimple.infoflow.android.resources.ARSCFileParser.AbstractResource;
import soot.jimple.infoflow.android.resources.ARSCFileParser.ResConfig;
import soot.jimple.infoflow.android.resources.ARSCFileParser.ResPackage;
import soot.jimple.infoflow.android.resources.ARSCFileParser.ResType;
import soot.jimple.infoflow.results.InfoflowResults;
import soot.jimple.infoflow.results.ResultSinkInfo;
import soot.jimple.infoflow.results.ResultSourceInfo;
import soot.jimple.internal.ImmediateBox;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.shimple.ShimpleExpr;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.Orderer;
import soot.toolkits.graph.PseudoTopologicalOrderer;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.LocalDefs;
import soot.util.queue.QueueReader;

public class FlowTriggerEventAnalyzer {
	public class MyFormatter extends Formatter {

	    /**
	     * @see java.util.logging.Formatter#format(java.util.logging.LogRecord)
	     */
	    @Override
	    public String format(final LogRecord record) {
	        return MessageFormat.format(record.getMessage(), record.getParameters());
	    }
	}

	public class EventRegisterElem{
		//In method, unit contains method, which is event listener register.
		//e.g., method: onCreate
		//      unit: $r1.setOnClickListener($r2)
		//      source: $r0.<com.android.insecurebankv2.DoLogin: android.content.Intent getIntent()>
		public SootMethod method; 
		public Unit unit;
		public ResultSourceInfo source;
		public EventRegisterElem(SootMethod m, Unit u, ResultSourceInfo source){
			this.method = m;
			this.unit = u;
			this.source = source;
		}
	}
	
	private static final Logger log = Logger.getLogger("NUFlow");
	{
		//for(Handler h : log.getHandlers())
		//	h.setFormatter(new MyFormatter());
		log.setLevel(Level.ALL);
	}
	private String[] EventNames = {
			"onClick", "onLongClick", "onFocusChange", "onKey", 
			"onTouch", "onKeyDown", "onKeyUp", "onTrackballEvent",
			"onTouchEvent", "onFocusChanged"};
	private Set<String> userEvents;
	
	private String[] SetEventListenerMethodNames = {
			"setOnDragListener", "setOnClickListener", "setOnApplyWindowInsetsListener",
			"setOnCreateContextMenuListener", "setOnEditorActionListener", "setOnFocusChangeListener",
			"setOnGenericMotionListener", "setOnHoverListener", "setOnKeyListener",
			"setOnLongClickListener", "setOnSystemUiVisibilityChangeListener", "setOnTouchListener"};
	private Set<String> setEventListenerMethods;
	private Map<Stmt, ResultSourceInfo> stmt2Source;
	private Set<Stmt> sourceStmts;
	private List<ResPackage> resourcePackages;
	private InfoflowResults savedInfoFlow;
	private HashMap<String, FlowTriggerEventObject> flowTriggerEventObjectMap;
	private String  apkFileLocation;
	private String appPackageName;
	ProcessManifest processMan;
	ARSCFileParser resParser;
	private Map<Integer, List<String>> id2Text;
	private Map<ResultSourceInfo, SootMethod> triggers ;
	private List<EventRegisterElem> eventRegisterElemList;
	private Map<ResultSourceInfo, List<String>> source2Texts;
	
	public FlowTriggerEventAnalyzer( InfoflowResults savedInfoFlow, String apkFileLocation){
		this.flowTriggerEventObjectMap = new HashMap<String, FlowTriggerEventObject>();
		this.savedInfoFlow = savedInfoFlow;
		if(savedInfoFlow == null){
			System.err.println("error: infoflow is null!");
		}
		this.apkFileLocation =  apkFileLocation;
		this.processMan = null;
		try{
			processMan = new ProcessManifest(apkFileLocation);
		}
		catch(Exception e){
			log.severe("failed to init FlowTriggerEventAnalyzer: ProcessManifest");
			e.printStackTrace();
		}
		this.appPackageName = processMan.getPackageName();
		
		resParser = new ARSCFileParser();
		try {
			resParser.parse(apkFileLocation);
		} catch (Exception e) {
			log.severe("failed to init FlowTriggerEventAnalyzer: ARSCFileParser");
			e.printStackTrace();
		}
		this.resourcePackages = resParser.getPackages();	
		id2Text = null;
		
		stmt2Source = new HashMap<Stmt, ResultSourceInfo>();
		sourceStmts = new HashSet<Stmt>();
		userEvents = new HashSet<String>(Arrays.asList(EventNames));
		setEventListenerMethods = new HashSet<String>(Arrays.asList(SetEventListenerMethodNames));
		triggers = new HashMap<ResultSourceInfo, SootMethod>();
		eventRegisterElemList = new ArrayList<EventRegisterElem>();
		source2Texts = new HashMap<ResultSourceInfo, List<String>>();
	}
	
	//DEBUG function, can be removed after testing.
	private Unit findConstructorInvokeStmt(Value objValue, Unit startingUnit, UnitGraph g){
		Set<Unit> visitedUnit = new HashSet<Unit>();
		Queue<Unit> q = new java.util.concurrent.LinkedBlockingQueue<Unit>();
		q.addAll(g.getSuccsOf(startingUnit));
		visitedUnit.add(startingUnit);
		
		while(!q.isEmpty()){
			Unit s = q.poll();
			visitedUnit.add(s);
			
			if(s instanceof InvokeStmt){
				InvokeStmt is = (InvokeStmt)s;
				InvokeExpr ie = is.getInvokeExpr();
				if(ie instanceof InstanceInvokeExpr){
					if(is.getInvokeExpr().getMethod().getName().equals("<init>") && 
							((InstanceInvokeExpr)ie).getBase().equivTo(objValue))
						return s;
				}
			}
			
			for(Unit child : g.getSuccsOf(s)){
				if (!visitedUnit.contains(child))
					q.add(child);
			}	
		}
		return null;
	}
	
	private Integer extractIDFromCallRetValue(CallRetValue crv){
		try{
			Pattern p = Pattern.compile("^\\d+$");
			if(crv.getMethod().getName().equals("findViewById")){
				Set<RightValue> args = crv.getArgs(0);
				for(RightValue a : args){
					if(a instanceof ConstantValue){
						ConstantValue c = (ConstantValue)a;
						String val = c.getOriginalValue().toString();
						Matcher m = p.matcher(val);
						if(m.matches()){
							//System.out.println("    found one ID: "+c.getOriginalValue().toString());
							return Integer.valueOf(val);
						}
					}
				}
			}
		}
		catch(Exception e){
			System.out.println("ERROR: extractIDFromCallRetValue: "+e);
		}
		return null;
	}
	
	//For A.setOnClickListener(B)
	//this method goes through all the findViewById methods: A = findViewById(ID)
	//then it can associates B and ID
	public void findFlowTriggerView(Map<SootMethod, IntraProcedureAnalysis> intraAnalysis){
		int count = 0;
		for(EventRegisterElem elem : eventRegisterElemList){
			count++;
			System.out.println("[NUTEXT] Start analyzing trigger texts for source: "+elem.source);
			SootMethod triggerMethod = triggers.get(elem.source);
			if(intraAnalysis.containsKey(elem.method)){
				IntraProcedureAnalysis analysis = intraAnalysis.get(elem.method);
				DefAnalysisMap dam = analysis.getFlowAfter(elem.unit);
				InvokeExpr expr = ((Stmt)elem.unit).getInvokeExpr();
				if(expr instanceof InstanceInvokeExpr){
					InstanceInvokeExpr iie = (InstanceInvokeExpr)expr;
					Value base = iie.getBase();
					Set<RightValue> rvs = dam.get(base);
					for(RightValue rv : rvs){
						//System.out.println("  RS: this flow's trigger is registered on: "+rv);
						if(rv instanceof CallRetValue){
							Integer id = extractIDFromCallRetValue((CallRetValue)rv);
							if(id != null){
								List<String> texts = id2Text.get(id);
								StringBuilder sb = new StringBuilder();
								if(texts != null){
									for(String text : texts)
										sb.append("{"+text+"} ");
								}
								if(sb.length() > 0){
									System.out.println("[NUTEXT] RS    ["+count+"] Source:"+elem.source+" || Texts:"+sb.toString());
									System.out.println("[NUTEXT] DETAIL["+count+"] Trigger:"+triggerMethod.getSignature()+" || ViewId:"+id);
								}
								else{
									System.out.println("[NUTEXT] ALERT  cannot find texts for view "+id);
								}
							}
							break;
						}
						else if(rv instanceof InstanceFieldValue){
							InstanceFieldValue ifv = (InstanceFieldValue)rv;
							for(SootMethod sm : intraAnalysis.keySet()){
								if(!sm.getName().equals(elem.method.getName()) &&
										sm.getDeclaringClass().getName().equals(elem.method.getDeclaringClass().getName())){	
									IntraProcedureAnalysis analysis2 = intraAnalysis.get(sm);
									if(!analysis2.getWriteFields().contains(ifv)) continue;
									List<Unit> units = analysis2.getGraph().getTails();
									for(Unit u : units){
										DefAnalysisMap dam2 = analysis2.getFlowAfter(u);
										if(dam2.containsKey(ifv)){
											Set<RightValue> rvs2 = dam2.get(ifv);
											for(RightValue rv2 : rvs2){
												if(rv2 instanceof CallRetValue){
													Integer id = extractIDFromCallRetValue((CallRetValue)rv2);
													if(id != null){
														List<String> texts = id2Text.get(id);
														StringBuilder sb = new StringBuilder();
														if(texts != null){
															for(String text : texts)
																sb.append("{"+text+"} ");
														}
														if(sb.length() > 0){
															System.out.println("[NUTEXT] RS    ["+count+"] Source:"+elem.source+" || Texts:"+sb.toString());
															System.out.println("[NUTEXT] DETAIL["+count+"] Trigger:"+triggerMethod.getSignature()+" || ViewId:"+id);
														}
														else{
															System.out.println("[NUTEXT] ALERT  cannot find texts for view "+id);
														}
													}
													break;
												}
													
											}
										}
									}
								}
								else{
									//System.out.println("    other method: "+sm);
								}
							}
						}
					}
				}
				else
					System.out.println("  ALERT: InvokeExpr is not InstanceInvokeExpr");
			}
			else{
				System.out.println("  ALERT: cannot find such this method's analysis:"+elem.method);
			}
		}
	}
	
	private SootMethod findPrecessorTrigger(SootMethod method){
		CallGraph cg = Scene.v().getCallGraph();
		ArrayDeque<SootMethod> queue = new ArrayDeque<SootMethod>();
		Set<String> visited = new HashSet<String>();
		SootMethod triggerMethod = null;
		queue.add(method);
		while(!queue.isEmpty()){
			SootMethod target = queue.poll();
			if(userEvents.contains(target.getName()) ){
				triggerMethod = target;
				break;
			}
			visited.add(target.getSignature());
			Iterator<Edge> edges = cg.edgesInto(target);
			while(edges.hasNext()){
				Edge edge = edges.next();
				SootMethod precessor = edge.getSrc().method();
				if(precessor == null)
					continue;
				//System.out.println("  CG:"+precessor+" => "+target);
				if(!visited.contains(precessor.getSignature()))
					queue.add(precessor);
			}
		}
		return triggerMethod;
	}
	
	private void analyzeFlowSroucesHelper(){
		CallGraph cg = Scene.v().getCallGraph();
		for(ResultSinkInfo sink: savedInfoFlow.getResults().keySet()){
			Set<ResultSourceInfo> sources = savedInfoFlow.getResults().get(sink);
			for(ResultSourceInfo source : sources){
				//System.out.println("SOURCE: "+source.getSource()+" M:");
				if(source.getSource().containsInvokeExpr()){
					InvokeExpr ie = source.getSource().getInvokeExpr();
					Iterator<Edge> edges = cg.edgesInto(ie.getMethod());				
					if(edges.hasNext()){
						SootMethod sm = findPrecessorTrigger(ie.getMethod());
						if(sm != null)
							triggers.put(source, sm);
					}
					else{
						stmt2Source.put(source.getSource(), source);
					}
				}
			}
		}
	}
	
	public void analyzeRegistrationCalls(){
		Map<String, String> view2Layout = new HashMap<String, String>();
		CallGraph cg = Scene.v().getCallGraph();
		//find all sources' triggers.
		analyzeFlowSroucesHelper();
		for (QueueReader<MethodOrMethodContext> rdr =
				Scene.v().getReachableMethods().listener(); rdr.hasNext(); ) {
			SootMethod m = rdr.next().method();
			if(!m.hasActiveBody())
				continue;
			UnitGraph g = new ExceptionalUnitGraph(m.getActiveBody());
		    LocalDefs localDefs = LocalDefs.Factory.newLocalDefs(g);
		    Orderer<Unit> orderer = new PseudoTopologicalOrderer<Unit>();
		    boolean changed = false;
		    //System.err.println("DEBUG=======================Start Method:"+m.getName()+" ==============");
		    for (Unit u : orderer.newList(g, false)) {
		    	Stmt s = (Stmt)u;
		    	if(stmt2Source.containsKey(s)){
		    		//note that for all the sources in sourceStmts,
		    		//we cannot find its precessor trigger via its method.
		    		//so we use its enclosing method.
		    		System.out.println("Found one source: "+s+" "+m+" // "+cg.edgesInto(m).hasNext());
		    		SootMethod sm = findPrecessorTrigger(m);
		    		if(sm != null) triggers.put(stmt2Source.get(s), sm);
		    	}
		    }
		}
		
		//find all triggers' event listener register units.
		HashMap<String, ResultSourceInfo> eventListenerClsMap = new HashMap<String, ResultSourceInfo>();
		for(ResultSourceInfo source : triggers.keySet()){
			SootMethod sm = triggers.get(source); //e.g., onClick
			if(sm.getDeclaringClass() != null)
				eventListenerClsMap.put(sm.getDeclaringClass().getType().toString(), source);
		}
		for (QueueReader<MethodOrMethodContext> rdr =
				Scene.v().getReachableMethods().listener(); rdr.hasNext(); ) {
			SootMethod m = rdr.next().method();
			if(!m.hasActiveBody())
				continue;
			UnitGraph g = new ExceptionalUnitGraph(m.getActiveBody());
		    Orderer<Unit> orderer = new PseudoTopologicalOrderer<Unit>();
		    for (Unit u : orderer.newList(g, false)) {
		    	Stmt s = (Stmt)u;
		    	if(s.containsInvokeExpr()){
		    		InvokeExpr expr = s.getInvokeExpr();
		    		SootMethod invokedM = expr.getMethod();
		    		if(setEventListenerMethods.contains(invokedM.getName())){
		    			if(invokedM.getParameterCount() == 1){ //e.g., setOnClickListener
		    				Value arg = expr.getArg(0); 
		    				String type = arg.getType().toString();
		    				if(eventListenerClsMap.containsKey(type)){
		    					System.out.println("DDD: "+invokedM+" "+type);
		    					eventRegisterElemList.add(new EventRegisterElem(m, u, eventListenerClsMap.get(type)));
		    				}
		    			}
		    		}
		    	}
		    	
		    }
		}
		
		LayoutFileParserForTextExtraction lfp = null;
		
		lfp = new LayoutFileParserForTextExtraction(this.appPackageName, resParser);
		lfp.parseLayoutFileForTextExtraction(apkFileLocation);	
		id2Text = lfp.getId2Texts();
		
		//update flowTriggerEventObject's text attributes
		for(String listenerClass : flowTriggerEventObjectMap.keySet()){
			FlowTriggerEventObject obj = flowTriggerEventObjectMap.get(listenerClass);
			System.out.println("DEBUG: EventListenerClass Name: "+listenerClass);
			for(EventOriginObject oo : obj.getEventOriginObjects()){
				//oo.setText(findResourceID());
				if(id2Text.containsKey(oo.getId()) ){
					List<String> tmp = id2Text.get(oo.getId());
					String texts = "";
					for(String s : tmp){
						if (texts.length() > 0)
							texts += "\n";
						texts += s.trim();
					}
					oo.setText(texts);
				}
				if(view2Layout.containsKey(oo.getDeclaringClass())){
					String layoutName = (String)view2Layout.get(oo.getDeclaringClass());
					if(lfp.getTextTreeMap().containsKey(layoutName)){
						oo.setDeclaringClsLayoutTextTree(lfp.getTextTreeMap().get(layoutName));
					}
				}
				System.out.println("DEBUG:  RS:"+oo.toString());
			}
			System.out.println();
		}
		
		for(ResultSourceInfo source : triggers.keySet()){
			System.out.println("TRIGGER: "+source+" => "+triggers.get(source));
		}
	}
	
	/* The type could be "id" or "string" */
	private int findResourceID(String name, String type){
		for(ARSCFileParser.ResPackage rp : resourcePackages){
			for (ResType rt : rp.getDeclaredTypes()){
				if(!rt.getTypeName().equals(type))
					continue;
				for (ResConfig rc : rt.getConfigurations())
					for (AbstractResource res : rc.getResources()){
						//System.err.println("DEBUG ID: "+res.getResourceName()+" => "+res.getResourceID());
						if (res.getResourceName().equalsIgnoreCase(name))
							return res.getResourceID();
					}
				}
		}
		return 0;
	}
	
	public InfoflowResults getSavedInfoFlow(){
		return this.savedInfoFlow;
	}
	public Map<String, FlowTriggerEventObject> getFlowTriggerEventObjectMap(){
		return this.flowTriggerEventObjectMap;
	}
	
	static public void displayGraph(UnitGraph g,String graphName, List<Unit> startingUnits, boolean reverse){
		if(startingUnits == null)
			startingUnits = g.getHeads();
		Queue<Pair<Unit, Integer>> queue = new java.util.concurrent.LinkedBlockingQueue<Pair<Unit, Integer>>();
		Set<Unit> visitedUnits = new HashSet<Unit>();
		System.err.println("DEBUG DisplayGraph: "+graphName);
		for(Unit su : startingUnits){
			if(!visitedUnits.contains(su)){
				queue.add(new Pair<Unit, Integer>(su, 1));
				visitedUnits.add(su);
			}
		}
		
		while(!queue.isEmpty()){
			Pair<Unit, Integer> item = queue.poll();
			String space = new String(new char[item.second*2]).replace('\0', ' ');
			System.err.println("  DEBUG G:"+space+item.first+" ");
			//if(item.second > 20)
			//	break;
			List<Unit> next = (reverse? g.getPredsOf(item.first) : g.getSuccsOf(item.first));
			for(Unit n : next){
				if(!visitedUnits.contains(n)){
					queue.add(new Pair<Unit, Integer>(n, item.second+1));
					visitedUnits.add(n);
				}
			}
		}
		System.err.println();
	}
}