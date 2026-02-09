package it.unisa.uniclass.orari.model;

import it.unisa.uniclass.utenti.model.Accademico;
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
    private Long id;

    /**
     * Corso di laurea a cui appartiene il corso
     * */
    @ManyToOne
    @JoinColumn(name = "corso_laurea_id")
    private CorsoLaurea corsoLaurea;

    /**
     * Lista delle lezioni associate al corso
     * */
    @OneToMany(mappedBy = "corso", cascade = CascadeType.ALL, fetch = FetchType.LAZY)
    private List<Lezione> lezioni;

    /**
     * Lista degli accademici (docenti) che insegnano il corso.
     * Relazione molti-a-molti: un corso può essere insegnato da più accademici,
     * e un accademico può insegnare più corsi.
     * */
    @ManyToMany(mappedBy = "corsi")
    private List<Accademico> accademici;

    /**
     * Anno didattico a cui appartiene il corso
     */
    @ManyToOne
    @JoinColumn(name = "anno_didattico_id", nullable = false)
    private AnnoDidattico annoDidattico;

    /**
     * Nome del Corso
     * */
    private String nome;

    /**
     * Restituisce l'anno didattico del corso.
     *
     * @return Anno didattico del corso
     */
    public AnnoDidattico getAnnoDidattico() {
        return annoDidattico;
    }

    /**
     * Imposta l'anno didattico del corso.
     *
     * @param annoDidattico Anno didattico
     */
    public void setAnnoDidattico(AnnoDidattico annoDidattico) {
        this.annoDidattico = annoDidattico;
    }



    // --- Costruttori ---

    /**
     * Costruttore che crea un corso con un nome specificato.
     *
     * @param nome Nome del corso.
     * */
    public Corso(String nome) {
        this.nome = nome;
        lezioni = new ArrayList<>();
        accademici = new ArrayList<>();
    }

    /**
     * Costruttore di default per creare un corso vuoto
     * */
    public Corso() {
        lezioni = new ArrayList<>();
        accademici = new ArrayList<>();
    }


    // --- Getters e Setters ---


    public List<Accademico> getAccademici() {
        return accademici;
    }
    public void setAccademici(List<Accademico> accademici) {
        this.accademici = accademici;
    }

    public Long getId() {
        return id;
    }

    public CorsoLaurea getCorsoLaurea() {
        return corsoLaurea;
    }
    public void setCorsoLaurea(CorsoLaurea corsoLaurea) {
        this.corsoLaurea = corsoLaurea;
    }

    public List<Lezione> getLezioni() {
        return lezioni;
    }
    public void setLezioni(List<Lezione> lezioni) {
        this.lezioni = lezioni;
    }

    public String getNome() {
        return nome;
    }
    public void setNome(String nome) {
        this.nome = nome;
    }



    @Override
    public String toString() {
        return "Corso{" +
                "id=" + id +
                ", corsoLaurea=" + corsoLaurea +
                ", accademici=" + accademici +
                ", nome='" + nome + '\'' +
                '}';
    }
}
