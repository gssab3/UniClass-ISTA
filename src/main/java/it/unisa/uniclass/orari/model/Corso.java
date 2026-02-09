package it.unisa.uniclass.orari.model;

import jakarta.persistence.*;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

/**
 * Classe che rappresenta un corso universitario.
 * Un corso è associato a un corso di laurea, lezioni, docenti e appelli d'esame.
 * */
@Entity
@Access(AccessType.FIELD)
@Table(name = "corsi")
@NamedQueries({
    @NamedQuery(name = "Corso.trovaCorso", query = "SELECT c FROM Corso c WHERE c.id = :id"),
    @NamedQuery(name = "Corso.trovaTutte", query = "SELECT c FROM Corso c"),
    @NamedQuery(name = "Corso.trovaCorsoLaurea", query = "SELECT c FROM Corso c WHERE c.corsoLaurea.nome = :nomeCorsoLaurea")
})
public class Corso implements Serializable {

    /**
     * Costante per identificare la query che cerca un corso per ID
     * */
    public static final String TROVA_CORSO = "Corso.trovaCorso";
    /**
     * Costante per identificare la query che restituisce tutti i corsi.
     * */
    public static final String TROVA_TUTTE = "Corso.trovaTutte";
    /**
     * Costante per identificare la query che restituisce i corsi di un determinato corso di laurea
     */
    public static final String TROVA_CORSI_CORSOLAUREA = "Corso.trovaCorsoLaurea";

    /**
     * Identificatore univoco del Corso
     * */
    @Id @GeneratedValue(strategy = GenerationType.IDENTITY)
    //@ spec_public
    //@ nullable
    private Long id;

    /**
     * Corso di laurea a cui appartiene il corso
     * */
    @ManyToOne
    @JoinColumn(name = "corso_laurea_id")
    //@ spec_public
    //@ nullable
    private CorsoLaurea corsoLaurea;

    /**
     * Lista delle lezioni associate al corso
     * */
    @OneToMany(mappedBy = "corso", cascade = CascadeType.ALL, fetch = FetchType.LAZY)
    //@ spec_public
    //@ nullable
    private List<Lezione> lezioni;

    /**
     * Lista dei docenti che insegnano il corso
     * */
    @ManyToMany(mappedBy = "corsi")
    //@ spec_public
    //@ nullable
    private List<Docente> docenti;

    /**
     * Anno didattico a cui appartiene il corso
     */
    @ManyToOne
    @JoinColumn(name = "anno_didattico_id", nullable = false)
    //@ spec_public
    //@ nullable
    private AnnoDidattico annoDidattico;

    /**
     * Nome del Corso
     * */
    //@ spec_public
    //@ nullable
    private String nome;

    /**
     * Restituisce l'anno didattico del corso.
     *
     * @return Anno didattico del corso
     */
    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == annoDidattico;
      @*/
    public /*@ nullable */ AnnoDidattico getAnnoDidattico() {
        return annoDidattico;
    }

    /**
     * Imposta l'anno didattico del corso.
     *
     * @param annoDidattico Anno didattico
     */
    /*@ public normal_behavior
      @ assignable this.annoDidattico;
      @ ensures this.annoDidattico == annoDidattico;
      @*/
    public void setAnnoDidattico(AnnoDidattico annoDidattico) {
        this.annoDidattico = annoDidattico;
    }




    /**
     * Costruttore che crea un corso con un nome specificato.
     *
     * @param nome Nome del corso.
     * */
    /*@ public normal_behavior
      @ assignable \everything;
      @ ensures this.nome == nome;
      @ ensures true;
      @*/
    public Corso(String nome) {
        this.nome = nome;
        lezioni = new ArrayList<>();
        docenti = new ArrayList<>();
    }

    /**
     * Costruttore di default per creare un corso vuoto
     * */
    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures true;
      @*/
    public Corso() {
        lezioni = new ArrayList<>();
        docenti = new ArrayList<>();
    }

    /**Restitusice la lista dei docenti associati al corso.
     *
     * @return Lista dei docenti
     * */
    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == docenti;
      @*/
    public /*@ nullable */ List<Docente> getDocenti() {
        return docenti;
    }

    /**
     * Imposta la lista dei docenti associati al corso.
     *
     * @param docenti Lista dei docenti.
     * */
    /*@ public normal_behavior
      @ assignable this.docenti;
      @ ensures this.docenti == docenti;
      @*/
    public void setDocenti(List<Docente> docenti) {
        this.docenti = docenti;
    }

    /**
     * Restituisce l'ID del corso.
     *
     * @return ID del corso
     * */
    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == id;
      @*/
    public /*@ nullable */ Long getId() {
        return id;
    }

    /**
     * Restituisce il corso di laurea associato al corso.
     *
     * @return Corso di laurea
     * */
    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == corsoLaurea;
      @*/
    public /*@ nullable */ CorsoLaurea getCorsoLaurea() {
        return corsoLaurea;
    }

    /**
     * Restituisce la lista delle lezioni del corso.
     *
     * @return Lista delle lezioni.
     * */
    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == lezioni;
      @*/
    public /*@ nullable */ List<Lezione> getLezioni() {
        return lezioni;
    }

    /**
     * Restituisce il nome del corso.
     *
     * @return Nome del corso.
     * */
    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == nome;
      @*/
    public /*@ nullable */ String getNome() {
        return nome;
    }

    /**
     * Imposta il corso di laurea associato al corso.
     *
     * @param corsoLaurea Corso di laurea.
     * */
    /*@ public normal_behavior
      @ assignable this.corsoLaurea;
      @ ensures this.corsoLaurea == corsoLaurea;
      @*/
    public void setCorsoLaurea(CorsoLaurea corsoLaurea) {
        this.corsoLaurea = corsoLaurea;
    }

    /**
     * Imposta la lista delle lezioni del corso.
     *
     * @param lezioni Lista delle lezioni.
     * */
    /*@ public normal_behavior
      @ assignable this.lezioni;
      @ ensures this.lezioni == lezioni;
      @*/
    public void setLezioni(List<Lezione> lezioni) {
        this.lezioni = lezioni;
    }

    /**
     * Imposta il nome del Corso
     *
     * @param nome Nome del corso
     * */
    /*@ public normal_behavior
      @ assignable this.nome;
      @ ensures this.nome == nome;
      @*/
    public void setNome(String nome) {
        this.nome = nome;
    }

    /**
     * Restituisce una rappresentazione in formato stringa del corso.
     *
     * @return Stringa che rappresenta il corso
     * */
    //@ skipesc
    @Override
    public String toString() {
        return "Corso{" +
                "id=" + id +
                ", corsoLaurea=" + corsoLaurea +
                ", docenti=" + docenti +
                ", nome='" + nome + '\'' +
                '}';
    }
}
