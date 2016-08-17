package soot.jimple.infoflow.android.nu;

import java.util.ArrayList;
import java.util.List;

public class FlowTriggerEventObject {
	
	public enum EventID{
		onClick
	}
	public class EventOriginObject{
		private String type;
		private String name;
		private String declaringClass;
		private int id = 0;
		private LayoutTextTreeNode declaringClsLayoutTextTree;
		private String text;
		
		//Some anonymous view doens't have name, but they must have an id used in findViewById(...)
		public EventOriginObject(String name, String type, String declaringClass, int id){
			this.type = type;
			this.name = name;
			this.declaringClass = declaringClass;
			this.id = id;
			this.declaringClsLayoutTextTree = null;
			this.text = null;
			
		}
		public String toString(){
			return "Type:"+type + 
					", Name:"+ ((name==null || name.equals("")) ? "empty" : name) +
					", Id:"+id +
					", Text:"+text+
					", Class:"+declaringClass+
					", ClsTree: \n"+(this.declaringClsLayoutTextTree==null?"null":this.declaringClsLayoutTextTree.toStringTree());
		}
		
		public LayoutTextTreeNode getDeclaringClsLayoutTextTree() {
			return declaringClsLayoutTextTree;
		}
		public void setDeclaringClsLayoutTextTree(
				LayoutTextTreeNode declaringClsLayoutTextTree) {
			this.declaringClsLayoutTextTree = declaringClsLayoutTextTree;
		}
		public String getText() {
			return text;
		}
		public void setText(String text) {
			this.text = text;
		}
		public String getType() {
			return type;
		}

		public void setType(String type) {
			this.type = type;
		}

		public String getName() {
			return name;
		}

		public void setName(String name) {
			this.name = name;
		}

		public String getDeclaringClass() {
			return declaringClass;
		}

		public void setDeclaringClass(String declaringClass) {
			this.declaringClass = declaringClass;
		}

		public int getId() {
			return id;
		}

		public void setId(int id) {
			this.id = id;
		}

	}

	public EventOriginObject createEventOriginObject(String name, String type, String declaringClass, int id){
		return new EventOriginObject(name, type, declaringClass, id);
	}
	
	final static public String onClickEventTriggerMethodName = "onClick";
	final static public String onClickRegisterMethodName = "setOnClickListener";
	
	private EventID eventID;
	private String registerMethodName;
	private List<EventOriginObject> eventOriginObjects;
	private String eventListenerClassName;
	
	public FlowTriggerEventObject(EventID id, String eventListenerClassName){
		this.eventID = id;
		switch (id){
			case onClick:
				this.registerMethodName = onClickRegisterMethodName;
				break;
			default:
				this.registerMethodName = null;
				break;
		}
		this.eventOriginObjects = new ArrayList<EventOriginObject>();
		this.eventListenerClassName = eventListenerClassName;
	}

	public String getRegisterMethodName() {
		return registerMethodName;
	}
	
	public List<EventOriginObject> getEventOriginObjects() {
		return eventOriginObjects;
	}
	
	public void addTriggerEventSrcObject(String name, String type, String declaringClass, int id){
		EventOriginObject srcObj = new EventOriginObject(name, type, declaringClass, id);
		this.eventOriginObjects.add(srcObj);
	}
	
	public void addTriggerEventSrcObject(EventOriginObject srcObj){
		this.eventOriginObjects.add(srcObj);
	}
	
	public String getEventListenerClassName(){
		return this.eventListenerClassName;
	}
	
	public boolean equals(Object another){
		if (! (another instanceof FlowTriggerEventObject))
			return false;
		return this.eventListenerClassName
				.equals(((FlowTriggerEventObject)another).getEventListenerClassName());
	}

}
