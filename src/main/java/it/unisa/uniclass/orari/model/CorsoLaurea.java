package it.unisa.uniclass.orari.model;

import jakarta.persistence.*;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * Classe che rappresenta un Corso di Laurea.
 * Contiene informazioni relative ai corsi, anni didattici e resti associati.
 * */
@Entity
@Access(AccessType.FIELD)
@NamedQueries({
        @NamedQuery(name = "CorsoLaurea.trovaCorsoLaurea", query = "SELECT c FROM CorsoLaurea c WHERE c.id = :id"),
        @NamedQuery(name = "CorsoLaurea.trovaTutti", query = "SELECT c FROM CorsoLaurea c"),
        @NamedQuery(name = "CorsoLaurea.trovaCorsoLaureaNome", query = "SELECT c FROM CorsoLaurea c WHERE c.nome = :nome")
})
public class CorsoLaurea implements Serializable {

    /**
     * Nome della query per trovare un corso di laurea tramite ID.
     * */
    public static final String TROVA_CORSOLAUREA = "CorsoLaurea.trovaCorsoLaurea";
    /**
     * Nome della query per trovare tutti i corsi di laurea
     * */
    public static final String TROVA_TUTTI = "CorsoLaurea.trovaTutti";
    /**
     * Nome per trovare un corso di laurea tramite nome.
     * */
    public static final String TROVA_CORSOLAUREA_NOME = "CorsoLaurea.trovaCorsoLaureaNome";

    /**
     * Identificativo unico del corso di laurea.
     * */
    @Id @GeneratedValue(strategy = GenerationType.IDENTITY)
    //@ spec_public
    //@ nullable
    private Long id;

    /**
     * Lista dei corsi associati a questo corso di laurea
     * */
    @OneToMany(mappedBy = "corsoLaurea", cascade = CascadeType.ALL, fetch = FetchType.LAZY)
    //@ spec_public
    //@ nullable
    private List<Corso> corsi = new ArrayList<>();

    /**
     * Nome del corso di laurea
     * */
    @Column(nullable = false, unique = true)
    //@ spec_public
    //@ nullable
    private String nome;

    /**
     * Lista dei resti associati al corso di laurea
     * */
    @OneToMany(mappedBy = "corsoLaurea", cascade = CascadeType.ALL)
    //@ spec_public
    //@ nullable
    private List<Resto> resti = new ArrayList<>(); // I resti associati al corso di laurea

    /**
     * Lista degli anni didattici assocaiti al corso di laurea
     * */
    @ManyToMany
    @JoinTable(
            name = "corso_laurea_anno_didattico",
            joinColumns = @JoinColumn(name = "corso_laurea_id"),
            inverseJoinColumns = @JoinColumn(name = "anno_didattico_id")
    )
    //@ spec_public
    //@ nullable
    private List<AnnoDidattico> anniDidattici = new ArrayList<>();

    /**
     * Lista degli studenti iscritti al corso di laurea.
     */
    @OneToMany(mappedBy = "corsoLaurea", cascade = CascadeType.ALL, fetch = FetchType.LAZY)
    //@ spec_public
    //@ nullable
    private List<Studente> studenti = new ArrayList<>();

    /**
     * Costruttore con il nome del corso di laurea
     *
     * @param nome Nome del corso di laurea
     * */
    /*@ public normal_behavior
      @ assignable \everything;
      @ ensures this.nome == nome;
      @ ensures true;
      @*/
    public CorsoLaurea(String nome) {
        this.nome = nome;
        this.corsi = new ArrayList<Corso>();
    }

    /**
     * Costruttore con nome, resti e anni didattici.
     *
     * @param nome Nome del corso di laurea
     * @param resti Lista dei resti associati
     * @param anniDidattici Lista degli anni didattici associati.
     * */
    /*@ public normal_behavior
      @ assignable \everything;
      @ ensures this.nome == nome;
      @ ensures this.resti == resti;
      @ ensures this.anniDidattici == anniDidattici;
      @*/
    public CorsoLaurea(String nome, List<Resto> resti, List<AnnoDidattico> anniDidattici) {
        this.nome = nome;
        this.corsi = new ArrayList<Corso>();
        this.resti = resti;
        this.anniDidattici = anniDidattici;
    }

    /**
     * Costruttore di default.
     * Inizializza liste vuote e il nome a null.
     * */
    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures true;
      @*/
    public CorsoLaurea() {
        this.corsi = new ArrayList<>();
        this.nome = null;
        this.resti = new ArrayList<>();
    }

    /**
     * Restituisce la lista dei resti associati
     *
     * @return Lista dei resti.
     * */
    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == resti;
      @*/
    public /*@ nullable */ List<Resto> getResti() {
        return resti;
    }

    /**Imposta la lista dei resti associati
     *
     * @param resti Lista dei resti da associare.
     * */
    /*@ public normal_behavior
      @ assignable this.resti;
      @ ensures this.resti == resti;
      @*/
    public void setResti(List<Resto> resti) {
        this.resti = resti;
    }

    /**
     * Restituisce la lista degli anni didattici associati.
     *
     * @return Lista degli anni didattici.
     */
    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == anniDidattici;
      @*/
    public /*@ nullable */ List<AnnoDidattico> getAnniDidattici() {
        return anniDidattici;
    }

    /**
     * Imposta la lista degli anni didattici associati.
     *
     * @param anniDidattici Lista degli anni didattici da associare.
     */
    /*@ public normal_behavior
      @ assignable this.anniDidattici;
      @ ensures this.anniDidattici == anniDidattici;
      @*/
    public void setAnniDidattici(List<AnnoDidattico> anniDidattici) {
        this.anniDidattici = anniDidattici;
    }

    /**
     * Restituisce l'ID del corso di laurea.
     *
     * @return ID del corso di laurea.
     * */
    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == id;
      @*/
    public /*@ nullable */ Long getId() {
        return id;
    }

    /**
     * Restituisce la lista dei corsi associati
     *
     * @return Lista dei corsi.
     * */
    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == corsi;
      @*/
    public /*@ nullable */ List<Corso> getCorsi() {
        return corsi;
    }

    /**
     * Restituisce il nome del corso di laurea.
     *
     * @return Nome del corso di laurea.
     */
    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == nome;
      @*/
    public /*@ nullable */ String getNome() {
        return nome;
    }

    /**
     * Imposta il nome del corso di laurea.
     *
     * @param nome Nome del corso di laurea da impostare.
     */
    /*@ public normal_behavior
      @ assignable this.nome;
      @ ensures this.nome == nome;
      @*/
    public void setNome(String nome) {
        this.nome = nome;
    }

    /**
     * Imposta la lista dei corsi associati.
     *
     * @param corsi Lista dei corsi da associare.
     */
    /*@ public normal_behavior
      @ assignable this.corsi;
      @ ensures this.corsi == corsi;
      @*/
    public void setCorsi(List<Corso> corsi) {
        this.corsi = corsi;
    }

    /**
     * Restituisce la lista degli studenti iscritti al corso di laurea.
     *
     * @return Lista degli studenti.
     */
    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == studenti;
      @*/
    public /*@ nullable */ Collection<Studente> getStudenti() {
        return studenti;
    }

    /**
     * Imposta la lista degli studenti iscritti al corso di laurea.
     *
     * @param studenti Lista degli studenti da associare.
     */
    /*@ public normal_behavior
      @ assignable this.studenti;
      @ ensures this.studenti == studenti;
      @*/
    public void setStudenti(List<Studente> studenti) {
        this.studenti = studenti;
    }

    /**
     * Rappresentazione testuale dell'oggetto CorsoLaurea.
     *
     * @return Stringa che descrive il corso di luarea.
     * */
    //@ skipesc
    @Override
    public String toString() {
        return "CorsoLaurea{" +
                "id=" + id +
                ", nome='" + nome + '\'' +
                '}';
    }
}
