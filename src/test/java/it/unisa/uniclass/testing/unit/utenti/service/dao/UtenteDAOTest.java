package it.unisa.uniclass.testing.unit.utenti.service.dao;

import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.dao.UtenteDAO;
import jakarta.persistence.EntityManager;
import jakarta.persistence.NoResultException;
import jakarta.persistence.TypedQuery;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Test Unitario per UtenteDAO.
 * Utilizza Mockito per simulare l'EntityManager e raggiungere il 100% di coverage.
 */
@ExtendWith(MockitoExtension.class)
class UtenteDAOTest {

    @Mock
    private EntityManager em;

    @Mock
    private TypedQuery<Utente> queryUtente; // Mock per query che restituiscono Utente

    @Mock
    private TypedQuery<Long> queryLong; // Mock per query che restituiscono Long (count)

    @InjectMocks
    private UtenteDAO utenteDAO;

    @Test
    @DisplayName("Create: deve chiamare persist")
    void testCreate() {
        Utente utente = new Utente();
        utenteDAO.create(utente);
        verify(em, times(1)).persist(utente);
    }

    @Test
    @DisplayName("Update: deve chiamare merge")
    void testUpdate() {
        Utente utente = new Utente();
        utenteDAO.update(utente);
        verify(em, times(1)).merge(utente);
    }

    /**
     * Test per Branch Coverage del metodo delete.
     * Caso 1: L'entità è già nel contesto di persistenza (em.contains restituisce true).
     * Il ramo 'if' viene saltato.
     */
    @Test
    @DisplayName("Delete: Entità già 'attached'")
    void testDelete_Attached() {
        Utente utente = new Utente();
        when(em.contains(utente)).thenReturn(true);

        utenteDAO.delete(utente);

        verify(em, times(1)).contains(utente);
        verify(em, never()).merge(any(Utente.class)); // Non deve fare il merge
        verify(em, times(1)).remove(utente);
    }

    /**
     * Test per Branch Coverage del metodo delete.
     * Caso 2: L'entità non è nel contesto (em.contains restituisce false).
     * Si entra nel ramo 'if', si fa il merge, e poi il remove.
     */
    @Test
    @DisplayName("Delete: Entità 'detached' (non gestita)")
    void testDelete_Detached() {
        Utente utente = new Utente();
        Utente managedUtente = new Utente(); // Istanza simulata restituita dal merge

        when(em.contains(utente)).thenReturn(false);
        when(em.merge(utente)).thenReturn(managedUtente);

        utenteDAO.delete(utente);

        verify(em, times(1)).contains(utente);
        verify(em, times(1)).merge(utente);
        verify(em, times(1)).remove(managedUtente); // Deve rimuovere l'istanza gestita
    }

    @Test
    @DisplayName("FindByEmail: Trovato con successo")
    void testFindByEmail_Success() {
        String email = "test@unisa.it";
        Utente expected = new Utente();
        expected.setEmail(email);

        // Configurazione catena Mock: createNamedQuery -> setParameter -> getSingleResult
        when(em.createNamedQuery("Utente.findByEmail", Utente.class)).thenReturn(queryUtente);
        when(queryUtente.setParameter("email", email)).thenReturn(queryUtente);
        when(queryUtente.getSingleResult()).thenReturn(expected);

        Utente result = utenteDAO.findByEmail(email);

        assertNotNull(result);
        assertEquals(email, result.getEmail());
    }

    @Test
    @DisplayName("FindByEmail: Non trovato (NoResultException) - Branch Coverage Catch")
    void testFindByEmail_NotFound() {
        String email = "nonusato@unisa.it";

        when(em.createNamedQuery("Utente.findByEmail", Utente.class)).thenReturn(queryUtente);
        when(queryUtente.setParameter("email", email)).thenReturn(queryUtente);
        when(queryUtente.getSingleResult()).thenThrow(new NoResultException());

        Utente result = utenteDAO.findByEmail(email);

        assertNull(result, "Deve ritornare null se lancia NoResultException");
    }

    @Test
    @DisplayName("FindAll: Restituisce lista")
    void testFindAll() {
        List<Utente> list = Collections.singletonList(new Utente());

        when(em.createNamedQuery("Utente.findAll", Utente.class)).thenReturn(queryUtente);
        when(queryUtente.getResultList()).thenReturn(list);

        List<Utente> result = utenteDAO.findAll();

        assertEquals(1, result.size());
    }

    @Test
    @DisplayName("Login: Successo")
    void testLogin_Success() {
        String email = "a@b.it";
        String pass = "pass";
        Utente u = new Utente();

        when(em.createNamedQuery("Utente.login", Utente.class)).thenReturn(queryUtente);
        when(queryUtente.setParameter(eq("email"), eq(email))).thenReturn(queryUtente);
        when(queryUtente.setParameter(eq("password"), eq(pass))).thenReturn(queryUtente);
        when(queryUtente.getSingleResult()).thenReturn(u);

        Utente result = utenteDAO.login(email, pass);
        assertNotNull(result);
    }

    @Test
    @DisplayName("Login: Fallimento (NoResultException) - Branch Coverage Catch")
    void testLogin_Failure() {
        when(em.createNamedQuery("Utente.login", Utente.class)).thenReturn(queryUtente);
        when(queryUtente.setParameter(anyString(), any())).thenReturn(queryUtente);
        when(queryUtente.getSingleResult()).thenThrow(new NoResultException());

        Utente result = utenteDAO.login("a", "b");
        assertNull(result);
    }

    @Test
    @DisplayName("ExistsByEmail: True")
    void testExistsByEmail() {
        String email = "test@exists.it";

        when(em.createNamedQuery("Utente.checkExists", Long.class)).thenReturn(queryLong);
        when(queryLong.setParameter("email", email)).thenReturn(queryLong);
        when(queryLong.getSingleResult()).thenReturn(1L); // Count > 0

        boolean result = utenteDAO.existsByEmail(email);
        assertTrue(result);
    }

    @Test
    @DisplayName("FindByTipo: Restituisce lista")
    void testFindByTipo() {
        String tipo = "Accademico";
        List<Utente> list = Collections.singletonList(new Utente());

        // Nota: Qui usiamo createQuery (non NamedQuery) come nel codice sorgente
        when(em.createQuery(anyString(), eq(Utente.class))).thenReturn(queryUtente);
        when(queryUtente.setParameter("tipo", tipo)).thenReturn(queryUtente);
        when(queryUtente.getResultList()).thenReturn(list);

        List<Utente> result = utenteDAO.findByTipo(tipo);
        assertFalse(result.isEmpty());
    }
}