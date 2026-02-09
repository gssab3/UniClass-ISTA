package it.unisa.uniclass.utenti.model;

import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.orari.model.Corso;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.model.Lezione;
import it.unisa.uniclass.orari.model.Resto;
import jakarta.persistence.*;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

@Entity
@Table(name = "accademico")
@NamedQueries({
        @NamedQuery(name = "Accademico.findAll", query = "SELECT a FROM Accademico a"),
        @NamedQuery(name = "Accademico.findByMatricola", query = "SELECT a FROM Accademico a WHERE a.matricola = :matricola"),
        @NamedQuery(name = "Accademico.findByRuolo", query = "SELECT a FROM Accademico a WHERE a.ruolo = :ruolo"),
        @NamedQuery(name = "Accademico.findByRuoloAndDip", query = "SELECT a FROM Accademico a WHERE a.ruolo = :ruolo AND a.dipartimento = :dipartimento")
})
public class Accademico extends Utente {

    private static final long serialVersionUID = 1L;

    // --- Attributi specifici di Accademico ---

    /** Relazione unidirezionale {@code @OneToOne}, mappata sul campo {@code corso_laurea_id}
     * */
    @Column(name = "matricola", unique = true)
    private String matricola;


    /**
     * Ruolo dell'Accademico, che può essere STUDENTE, DOCENTE o COORDINATORE. Utilizzato per differenziare i tipi di utenti accademici e gestire le autorizzazioni.
     */
    @Enumerated(EnumType.STRING)
    @Column(name = "ruolo", nullable = false)
    private Ruolo ruolo; // STUDENTE, DOCENTE, COORDINATORE

    /** Dipartimento di appartenenza dell'Accademico (es. "Ingegneria Informatica")
     * */
    @Column(name = "dipartimento")
    private String dipartimento;

    /**
     * Corso di Laurea dell'Accademico.
     * Relazione molti-a-uno: più accademici possono iscriversi allo stesso corso di laurea.
     */
    @ManyToOne
    @JoinColumn(name = "corso_laurea_id")
    private CorsoLaurea corsoLaurea;

    /**
     * Indica se l'account dell'accademico è attivato o meno. Utile per gestire il processo di attivazione degli account.
     */
    @Column(name = "attivato")
    private boolean attivato;


    /**
     * Resto associato all'accademico, utilizzato per indicare informazioni extra.
     * Relazione uno-a-molti.
     * */
    @ManyToOne
    @JoinColumn(name = "resto", nullable = true)
    private Resto resto;


    /** Relazione unidirezionale {@code @OneToMany}, con cascata totale e rimozione orfana
     * */
    @OneToMany(mappedBy = "autore", cascade = CascadeType.ALL, orphanRemoval = true)
    private Set<Messaggio> messaggiInviati = new HashSet<>();

    /** Relazione unidirezionale {@code @OneToMany}, con cascata totale e rimozione orfana.
     */
    @OneToMany(mappedBy = "destinatario", cascade = CascadeType.ALL, orphanRemoval = true)
    private Set<Messaggio> messaggiRicevuti = new HashSet<>();

    /**
     * Corsi insegnati o seguiti attualmente dall'accademico
     * */
    @ManyToMany
    @JoinTable(
            name = "accademico_corso",
            joinColumns = @JoinColumn(name = "accademico_id"),
            inverseJoinColumns = @JoinColumn(name = "corso_id")
    )
    protected List<Corso> corsi = new ArrayList<>();


    /**
     * Lezioni presidiate
     * */
    @ManyToMany
    @JoinTable(
            name = "docente_lezione",
            joinColumns = @JoinColumn(name = "docente_id"),
            inverseJoinColumns = @JoinColumn(name = "lezione_id")
    )
    private List<Lezione> lezioni = new ArrayList<>();


    // --- Costruttori ---

    public Accademico() {
        super();
    }

    public Accademico(String email, String password, String nome, String cognome, LocalDate dataNascita, String telefono,
                      String matricola, Ruolo ruolo, String dipartimento) {
        setEmail(email);
        setTelefono(telefono);
        setNome(nome);
        setCognome(cognome);
        setDataNascita(dataNascita);
        setPassword(password);
        this.matricola = matricola;
        this.ruolo = ruolo;
        this.dipartimento = dipartimento;
        this.attivato = false; // Default a false se richiede attivazione
    }

    // --- Getter e Setter ---

    public String getMatricola() { return matricola; }
    public void setMatricola(String matricola) { this.matricola = matricola; }

    public Ruolo getRuolo() { return ruolo; }
    public void setRuolo(Ruolo ruolo) { this.ruolo = ruolo; }

    public String getDipartimento() { return dipartimento; }
    public void setDipartimento(String dipartimento) { this.dipartimento = dipartimento; }

    public CorsoLaurea getCorsoLaurea() { return this.corsoLaurea; }
    public void setCorsoLaurea(CorsoLaurea corsoLaurea) { this.corsoLaurea = corsoLaurea; }

    public boolean isAttivato() { return attivato; }
    public void setAttivato(boolean attivato) { this.attivato = attivato; }

    public Resto getResto() {return resto;}
    public void setResto(Resto resto) {this.resto = resto;}

    public Set<Messaggio> getMessaggiInviati() {return messaggiInviati;}
    public void setMessaggiInviati(Set<Messaggio> messaggiInviati) {this.messaggiInviati = messaggiInviati;}

    public Set<Messaggio> getMessaggiRicevuti() {return messaggiRicevuti;}
    public void setMessaggiRicevuti(Set<Messaggio> messaggiRicevuti) {this.messaggiRicevuti = messaggiRicevuti;}

    public List<Corso> getCorsi() {return corsi;}
    public void setCorsi(List<Corso> corsi) {this.corsi = corsi;}

    public List<Lezione> getLezioni() {return lezioni;}
    public void setLezioni(List<Lezione> lezioni) {this.lezioni = lezioni;}


    @Override
    public String toString() {
        return "Accademico{" +
                "matricola='" + matricola + '\'' +
                ", ruolo=" + ruolo +
                ", dipartimento='" + dipartimento + '\'' +
                ", corsoLaurea=" + corsoLaurea +
                ", attivato=" + attivato +
                ", resto=" + resto +
                ", messaggiInviati=" + messaggiInviati +
                ", messaggiRicevuti=" + messaggiRicevuti +
                ", corsi=" + corsi +
                ", lezioni=" + lezioni +
                '}';
    }
}